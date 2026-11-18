-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.realizer_native_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T21:06:59.528675+00:00
-- url     : https://prove2.me/submissions/f43d6449-90b7-42d2-9e17-659b243bdf9f

import Definitions.Def_OAIThreeMachineSched02
import Mathlib
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding

-- Solutions.TreeStackCompiler
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical

/- Reused compiler proofs from the accepted public OAI.ThreeMachine.main_theorem
    submission, under the platform Apache-2.0 license. -/

section
-- module StackMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

theorem head_stackTape (xs : List Bool) : unsymbol (stackTape xs).head = xs.head? := by
  cases xs with
  | nil => rfl
  | cons b xs => exact unsymbol_symbol b

theorem tape_two_phases (a : Action) (xs : List Bool) :
    applyTape (phaseTwo a (middleTape a xs).head) (middleTape a xs) = stackTape (a.apply xs) := by
  cases a with
  | stay => simp [applyTape, phaseTwo, middleTape, phaseOne, Action.apply]
  | pop =>
    change (((stackTape xs).write 0).move .right).write
      (((stackTape xs).write 0).move .right).head = stackTape xs.tail
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.write_mk',
      Turing.Tape.move_right_mk', Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      blank_cons]
    cases xs <;> rfl
  | push b =>
    change (((stackTape xs).write (stackTape xs).head).move .left).write (symbol b) =
      stackTape (b :: xs)
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.move_left_mk',
      Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
      List.tail_nil, List.tail_cons, List.map_cons, Turing.ListBlank.cons_mk]

section Compilation
variable {k : ℕ} {Q : Type} [Fintype Q] (P : Program k Q)

theorem step_ready {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    (compile P).step c =
      (P.transition s.control (fun j => (s.store j).head?)).map (fun qa => middleCfg qa s.store) := by
  have ht : (fun j => unsymbol (c.tapes j).head) = fun j => (s.store j).head? := by
    funext j
    rw [h.2 j, head_stackTape]
  unfold Machine.step compile
  simp only [h.1, ht]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none => rfl
  | some qa =>
    apply congrArg some
    congr 1
    funext j
    dsimp only
    rw [h.2 j]
    rfl

theorem step_middle (qa : Q × Actions k) (s : Store k) :
    (compile P).step (middleCfg qa s) =
      some (readyCfg ⟨qa.1,fun j => (qa.2 j).apply (s j)⟩) := by
  unfold Machine.step compile middleCfg
  simp only [read_numberControl]
  apply congrArg some
  congr 1
  funext j
  exact tape_two_phases (qa.2 j) (s j)

theorem halted_iff {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) : (compile P).step c = none ↔ P.step s = none := by
  rw [step_ready P h]
  unfold Program.step
  cases P.transition s.control (fun j => (s.store j).head?) <;> simp

theorem two_steps {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2] c) ((P.step s).getD s) := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [step_ready P h]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [step_ready P h, he]
    simpa [Program.step, he] using h
  | some qa =>
    simp only [Option.map_some, Option.getD_some, step_middle]
    simp [Program.step, he]

theorem simulate {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) (n : ℕ) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2*n] c)
      ((fun d => (P.step d).getD d)^[n] s) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2*n) 2, Function.iterate_add_apply]
    simpa only [Function.iterate_succ_apply'] using two_steps P ih

theorem relates_initial (input : List Bool) :
    Relates P ((compile P).initial input) ⟨P.initial, initialStore input⟩ := by
  refine ⟨read_zero P, ?_⟩
  intro i
  change Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) =
    Turing.Tape.mk₁ ((if i = 0 then input else []).map symbol)
  split_ifs <;> rfl

theorem simulate_initial (input : List Bool) (n : ℕ) :
    Relates P ((compile P).run input (2*n)) (P.run (initialStore input) n) :=
  simulate P (relates_initial P input) n

theorem compile_produces (input out : List Bool) (bound : ℕ)
    (h : ∃ n ≤ bound, P.step (P.run (initialStore input) n) = none ∧
      (P.run (initialStore input) n).store 0 = out) :
    (compile P).Produces input out (2*bound) := by
  obtain ⟨n,hn,hh,ho⟩ := h
  have hs := simulate_initial P input n
  refine ⟨2*n, by omega, (halted_iff P hs).mpr hh, ?_⟩
  rw [hs.2 0, ho]
  exact Turing.Tape.mk'_right₀ _ _

end Compilation
namespace Program
variable {k : ℕ} {Q R S : Type}

theorem Exec.iterate {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : (fun c => (P.step c).getD c)^[n] s = t := by
  induction h with
  | halt => rfl
  | next he _ ih => simpa only [Function.iterate_succ_apply, he, Option.getD_some] using ih

theorem Exec.halted {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : P.step t = none := by
  induction h with
  | halt h => exact h
  | next _ _ ih => exact ih

theorem Exec.continue {P : Program k Q} {P' : Program k R} (f : Q → R)
    (hs : ∀ s t, P.step s = some t →
      P'.step (State.mapControl f s) = some (State.mapControl f t))
    {s t : State k Q} {u : State k R} {n m : ℕ} (h : Exec P s n t)
    (ht : Exec P' (State.mapControl f t) m u) :
    Exec P' (State.mapControl f s) (n+m) u := by
  induction h with
  | halt => simpa only [Nat.zero_add] using ht
  | next he _ ih => simpa only [Nat.add_right_comm] using Exec.next (hs _ _ he) (ih ht)

theorem lift_step (P : Program k Q) (P' : Program k R) (f : Q → R)
    (h : ∀ q heads q' a, P.transition q heads = some (q',a) →
      P'.transition (f q) heads = some (f q',a))
    (s t : State k Q) (he : P.step s = some t) :
    P'.step (State.mapControl f s) = some (State.mapControl f t) := by
  unfold step at he
  cases hh : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [hh] at he
  | some qa =>
    have het : t = ⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [hh] using he.symm
    subst t
    simp [step, State.mapControl, h _ _ _ _ hh]

theorem seq_left_step (P : Program k Q) (P' : Program k R)
    (s t : State k Q) (h : P.step s = some t) :
    (seq P P').step (State.mapControl Sum.inl s) = some (State.mapControl Sum.inl t) := by
  apply lift_step P (seq P P') Sum.inl _ s t h
  intro q heads q' a ha
  simp [seq,ha]

theorem seq_right_exec (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (seq P P') (State.mapControl Sum.inr s) n (State.mapControl Sum.inr t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;> simp_all [seq,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (seq P P') Sum.inr _ _ _ he
    intro q heads q' a ha
    simp [seq, ha]

theorem seq_exec {P : Program k Q} {P' : Program k R} {s t : Store k}
    {q : Q} {r : R} {n m : ℕ} (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    {u : Store k} (h' : Exec P' ⟨P'.initial,t⟩ m ⟨r,u⟩) :
    Exec (seq P P') ⟨(seq P P').initial,s⟩ (n+m+1) ⟨Sum.inr r,u⟩ := by
  have hh := h.halted
  have hs : (seq P P').step ⟨Sum.inl q,t⟩ = some ⟨Sum.inr P'.initial,t⟩ := by
    unfold step at hh ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;> simp_all [seq, stayActions,Action.apply]
  have hx := h.continue Sum.inl (seq_left_step P P') (Exec.next hs (seq_right_exec P h'))
  simpa only [State.mapControl, seq, Nat.add_assoc] using hx

theorem instruction_exec (a : Heads k → Actions k) (s : Store k) :
    Exec (instruction a) ⟨false,s⟩ 1
      ⟨true,fun i => (a (fun j => (s j).head?) i).apply (s i)⟩ := by
  apply Exec.next (by rfl)
  exact Exec.halt rfl

theorem loop_body_step (test : Heads k → Bool) (P : Program k Q)
    (s t : State k Q) (h : P.step s = some t) :
    (loop test P).step (State.mapControl some s) = some (State.mapControl some t) := by
  apply lift_step P (loop test P) some _ s t h
  intro q heads q' a ha
  simp [loop,ha]

theorem loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (h : test (fun i => (s i).head?) = false) :
    Exec (loop test P) ⟨none,s⟩ 0 ⟨none,s⟩ := by
  exact Exec.halt (by simp [step,loop,h])

theorem loop_iterate (test : Heads k → Bool) {P : Program k Q} {s t u : Store k}
    {q : Q} {n m : ℕ} (hs : test (fun i => (s i).head?) = true)
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    (hrest : Exec (loop test P) ⟨none,t⟩ m ⟨none,u⟩) :
    Exec (loop test P) ⟨none,s⟩ (n+m+2) ⟨none,u⟩ := by
  have hstart : (loop test P).step ⟨none,s⟩ = some ⟨some P.initial,s⟩ := by
    simp [step,loop,hs,stayActions,Action.apply]
  have hhalt := h.halted
  have hend : (loop test P).step ⟨some q,t⟩ = some ⟨none,t⟩ := by
    unfold step at hhalt ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;>
      simp_all [loop,stayActions,Action.apply]
  have hb := h.continue some (loop_body_step test P) (Exec.next hend hrest)
  convert Exec.next hstart hb using 1
  omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Program
variable {k : ℕ}

theorem transfer_instruction {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (transferActions src dst)) ⟨false,s⟩ 1
      ⟨true,transferOnce src dst b xs s⟩ := by
  have h := instruction_exec (transferActions src dst) s
  convert h using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i
    simp [transferOnce, transferActions, hne, hs, Action.apply]
  · by_cases hd : i = dst
    · subst i
      simp [transferOnce, transferActions, hne.symm, hs, Action.apply]
    · simp [transferOnce, transferActions,hi,hd,Action.apply]

theorem transfer_result_once {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    transferResult src dst (transferOnce src dst b xs s) = transferResult src dst s := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [transferResult,transferOnce,hne,hs,List.reverse_cons,List.append_assoc]
  · by_cases hsrc : i = src
    · subst i
      simp [transferResult,transferOnce,hne]
    · simp [transferResult,transferOnce,hi,hsrc]

theorem transfer_exec {src dst : Fin (k+1)} (hne : src ≠ dst) (s : Store k) :
    Exec (transfer src dst) ⟨none,s⟩ (3*(s src).length) ⟨none,transferResult src dst s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : transferResult src dst s = s := by
      funext i
      by_cases hd : i = dst
      · subst i; simp [transferResult,he]
      · by_cases hs : i = src
        · subst i; simp [transferResult,he,hne]
        · simp [transferResult,hd,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := transferOnce src dst b xs s
    have hs' : s' src = xs := by simp [s',transferOnce,hne]
    have hrest := ih s' hs'
    rw [transfer_result_once hne b xs s he] at hrest
    have hbody := transfer_instruction hne b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem pop_instruction (src : Fin (k+1)) (s : Store k) :
    Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1
      ⟨true,Function.update s src (s src).tail⟩ := by
  convert instruction_exec (fun _ => popActions src) s using 1
  congr 1
  funext i
  by_cases h : i = src <;> simp [popActions,Action.apply,h]

theorem clear_exec (src : Fin (k+1)) (s : Store k) :
    Exec (clear src) ⟨none,s⟩ (3*(s src).length) ⟨none,Function.update s src []⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : Function.update s src [] = s := by rw [← he]; exact Function.update_eq_self _ _
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := Function.update s src xs
    have hrest := ih s' (by simp [s'])
    have hu : Function.update s' src [] = Function.update s src [] := by simp [s']
    rw [hu] at hrest
    have hbody : Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1 ⟨true,s'⟩ := by
      simpa only [he,List.tail_cons] using pop_instruction src s
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

theorem spread_instruction {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (spreadActions src dst₁ dst₂)) ⟨false,s⟩ 1
      ⟨true,spreadOnce src dst₁ dst₂ b xs s⟩ := by
  convert instruction_exec (spreadActions src dst₁ dst₂) s using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i; simp [spreadOnce,spreadActions,h₁,h₂,hs,Action.apply]
  · by_cases hdi : i = dst₁
    · subst i; simp [spreadOnce,spreadActions,h₁.symm,h₃,hs,Action.apply]
    · by_cases hdj : i = dst₂
      · subst i; simp [spreadOnce,spreadActions,h₂.symm,hs,Action.apply]
      · simp [spreadOnce,spreadActions,hi,hdi,hdj,Action.apply]

theorem spread_result_once {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    spreadResult src dst₁ dst₂ (spreadOnce src dst₁ dst₂ b xs s) = spreadResult src dst₁ dst₂ s := by
  funext i
  by_cases hi : i = dst₂
  · subst i
    simp [spreadResult,spreadOnce,h₁,h₂,hs,List.reverse_cons,List.append_assoc]
  · by_cases hd : i = dst₁
    · subst i
      simp [spreadResult,spreadOnce,h₁,h₂,h₃,hs,List.reverse_cons,List.append_assoc]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,spreadOnce,h₁,h₂]
      · simp [spreadResult,spreadOnce,hi,hd,hsrc]

theorem spread_exec {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂) (s : Store k) :
    Exec (spread src dst₁ dst₂) ⟨none,s⟩ (3*(s src).length) ⟨none,spreadResult src dst₁ dst₂ s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : spreadResult src dst₁ dst₂ s = s := by
      funext i
      by_cases hd₂ : i = dst₂
      · subst i; simp [spreadResult,he]
      · by_cases hd₁ : i = dst₁
        · subst i; simp [spreadResult,he,h₃]
        · by_cases hs : i = src
          · subst i; simp [spreadResult,he,h₁,h₂]
          · simp [spreadResult,hd₁,hd₂,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := spreadOnce src dst₁ dst₂ b xs s
    have hs' : s' src = xs := by simp [s',spreadOnce,h₁,h₂]
    have hrest := ih s' hs'
    rw [spread_result_once h₁ h₂ h₃ b xs s he] at hrest
    have hbody := spread_instruction h₁ h₂ h₃ b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

theorem prepend_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (prepend src dst tmp) ⟨(prepend src dst tmp).initial,s⟩
      (6*(s src).length+1) ⟨Sum.inr none,Function.update s dst (s src ++ s dst)⟩ := by
  have hx := seq_exec (transfer_exec h₂ s)
    (spread_exec h₂.symm h₃.symm h₁ (transferResult src tmp s))
  have hl : (transferResult src tmp s tmp).length = (s src).length := by simp [transferResult,htmp]
  have he : spreadResult tmp src dst (transferResult src tmp s) =
      Function.update s dst (s src ++ s dst) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [spreadResult,transferResult,htmp,h₃,h₁.symm]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,transferResult,htmp,h₂,h₁]
      · by_cases ht : i = tmp
        · subst i; simp [spreadResult,transferResult,htmp,h₂.symm,h₃.symm]
        · simp [spreadResult,transferResult,hd,hsrc,ht]
  rw [he,hl] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem copy_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (copy src dst tmp) ⟨(copy src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update s dst (s src)⟩ := by
  have hx := seq_exec (clear_exec dst s)
    (prepend_exec h₁ h₂ h₃ (Function.update s dst []) (by simp [h₃.symm,htmp]))
  simpa [copy,h₁,Nat.add_assoc] using hx

end ThreeMachine.StackCompiler.Program

end

end OAI
end

section
-- module TreeData
namespace OAI

section

namespace ThreeMachine.StackCompiler

namespace Data

end Data

namespace Program
variable {k : ℕ}

theorem scan_instruction {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (s : Store k) (b : Bool) (rest : List Bool) (hs : s src = b :: rest) :
    Exec (instruction (scanActions src dst ct)) ⟨false,s⟩ 1 ⟨true,scanOnce src dst ct s b rest⟩ := by
  convert instruction_exec (scanActions src dst ct) s using 1
  congr 1
  funext i
  by_cases hi : i = ct
  · subst i; cases b <;> simp [scanActions,scanOnce,hs,h₂.symm,h₃.symm,Action.apply]
  · by_cases hd : i = dst
    · subst i; simp [scanActions,scanOnce,hs,hi,h₁.symm,Action.apply]
    · by_cases hsrc : i = src
      · subst i; simp [scanActions,scanOnce,hs,h₁,h₂,Action.apply]
      · simp [scanActions,scanOnce,hi,hd,hsrc,Action.apply]

theorem scanned_scanned {src dst ct : Fin (k+1)}
    (h₃ : dst ≠ ct) (s : Store k) (rest mid w₁ w₂ : List Bool) (c d : ℕ) :
    scanned src dst ct (scanned src dst ct s mid w₁ d) rest w₂ c =
      scanned src dst ct s rest (w₁ ++ w₂) c := by
  funext i
  by_cases hc : i = ct
  · subst i; simp [scanned]
  · by_cases hd : i = dst
    · subst i; simp [scanned,h₃,List.reverse_append,List.append_assoc]
    · by_cases hs : i = src
      · subst i; simp [scanned,hc,hd]
      · simp [scanned,hc,hd,hs]

theorem scan_tree_continue {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct) (d : Data) :
    ∀ (s t : Store k) (rest : List Bool) (c m : ℕ),
      s src = d.encode ++ rest → s ct = List.replicate (c+1) true →
      Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode c⟩ m ⟨none,t⟩ →
      Exec (scan src dst ct) ⟨none,s⟩ (3*d.size+m) ⟨none,t⟩ := by
  induction d with
  | nil =>
    intro s t rest c m hs hc hrest
    have hsrc : s src = false :: rest := by simpa using hs
    have he : scanOnce src dst ct s false rest = scanned src dst ct s rest [false] c := by
      simp [scanOnce,scanned,hc,List.replicate_succ]
    have hbody := scan_instruction h₁ h₂ h₃ s false rest hsrc
    rw [he] at hbody
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [Data.size_nil]; omega
  | pair a b iha ihb =>
    intro s t rest c m hs hc hrest
    let s₁ := scanOnce src dst ct s true (a.encode ++ b.encode ++ rest)
    have hs₁ : s₁ src = a.encode ++ (b.encode ++ rest) := by
      simp [s₁,scanOnce,h₁,h₂,List.append_assoc]
    have hc₁ : s₁ ct = List.replicate (c+2) true := by
      simp [s₁,scanOnce,hc,List.replicate_succ]
    let s₂ := scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1)
    have hs₂ : s₂ src = b.encode ++ rest := by simp [s₂,scanned,h₁,h₂]
    have hc₂ : s₂ ct = List.replicate (c+1) true := by simp [s₂,scanned]
    have hend : scanned src dst ct s₂ rest b.encode c =
        scanned src dst ct s rest (Data.pair a b).encode c := by
      rw [show s₂ = scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1) by rfl,
        scanned_scanned h₃]
      funext i
      by_cases hi : i = ct
      · subst i; simp [scanned]
      · by_cases hd : i = dst
        · subst i; simp [scanned,s₁,scanOnce,h₃,List.reverse_cons,List.reverse_append,
            Data.encode,List.append_assoc]
        · by_cases hsrc : i = src
          · subst i; simp [scanned,hi,hd]
          · simp [scanned,s₁,scanOnce,hi,hd,hsrc]
    have hafterB := ihb s₂ t rest c m hs₂ hc₂ (by rwa [hend])
    have hafterA := iha s₁ t (b.encode ++ rest) (c+1) (3*b.size+m) hs₁ hc₁ hafterB
    have hsrc : s src = true :: (a.encode ++ b.encode ++ rest) := by
      simpa [Data.encode,List.append_assoc] using hs
    have hbody := scan_instruction h₁ h₂ h₃ s true _ hsrc
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hafterA
    convert hx using 1 <;> first | rfl | rw [Data.size_pair]; omega

theorem scan_tree {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (d : Data) (s : Store k) (rest : List Bool)
    (hs : s src = d.encode ++ rest) (hc : s ct = [true]) :
    Exec (scan src dst ct) ⟨none,s⟩ (3*d.size)
      ⟨none,scanned src dst ct s rest d.encode 0⟩ := by
  have hstop : Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode 0⟩ 0
      ⟨none,scanned src dst ct s rest d.encode 0⟩ :=
    loop_stop _ _ _ (by simp [scanned])
  simpa using scan_tree_continue h₁ h₂ h₃ d s _ rest 0 0 hs (by simpa using hc) hstop

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q R : Type}

theorem Exec.runs {P : Program k Q} {s t : Store k} {n : ℕ} {q : Q}
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩) : P.Runs s t n := ⟨n,le_rfl,q,h⟩

theorem Runs.mono {P : Program k Q} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := by
  obtain ⟨t',ht',q,hq⟩ := h
  exact ⟨t',ht'.trans hnm,q,hq⟩

theorem Runs.computes {P : Program k Q} {s t : Store k} {n : ℕ}
    (h : P.Runs s t n) : P.Computes s t n := by
  obtain ⟨m,hm,q,hq⟩ := h
  refine ⟨m,hm,?_,?_⟩
  · exact congrArg State.store hq.iterate
  · unfold run
    rw [hq.iterate]
    exact hq.halted

theorem Runs.seq {P : Program k Q} {P' : Program k R} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (seq P P').Runs s u (n+m+1) := by
  obtain ⟨n',hn',q,hq⟩ := h
  obtain ⟨m',hm',r,hr⟩ := h'
  exact (seq_exec hq hr).runs.mono (by omega)

theorem branch_left_exec (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : State k Q} {n : ℕ} (h : Exec P s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inl) s) n
      (State.mapControl (some ∘ Sum.inl) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P (branch test P P') (some ∘ Sum.inl) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem branch_right_exec (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inr) s) n
      (State.mapControl (some ∘ Sum.inr) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (branch test P P') (some ∘ Sum.inr) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem Runs.branch_left (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : Store k} {n : ℕ} (h : P.Runs s t n) (ht : test (fun i => (s i).head?) = true) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inl P.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inl q),Exec.next hs (branch_left_exec test P' hq)⟩

theorem Runs.branch_right (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : Store k} {n : ℕ} (h : P'.Runs s t n) (ht : test (fun i => (s i).head?) = false) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inr P'.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inr q),Exec.next hs (branch_right_exec test P hq)⟩

theorem move_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (move src dst tmp) ⟨(move src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update (Function.update s src []) dst (s src)⟩ := by
  let s₁ := Function.update s dst []
  let s₂ := transferResult src tmp s₁
  have hx := seq_exec (clear_exec dst s)
    (seq_exec (transfer_exec h₂ s₁) (transfer_exec h₃.symm s₂))
  have hl₁ : s₁ src = s src := by simp [s₁,h₁]
  have hl₂ : (s₂ tmp).length = (s src).length := by simp [s₂,s₁,transferResult,h₁,h₃.symm,htmp]
  have he : transferResult tmp dst s₂ = Function.update (Function.update s src []) dst (s src) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [transferResult,s₂,s₁,h₃,h₃.symm,htmp,h₁,h₁.symm]
    · by_cases ht : i = tmp
      · subst i; simp [transferResult,s₂,s₁,h₃.symm,htmp,h₁,h₂.symm]
      · by_cases hsrc : i = src
        · subst i; simp [transferResult,s₂,s₁,h₁,h₂]
        · simp [transferResult,s₂,s₁,hd,ht,hsrc]
  rw [he,hl₁,hl₂] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem push_exec (dst : Fin (k+1)) (b : Bool) (s : Store k) :
    Exec (push dst b) ⟨false,s⟩ 1 ⟨true,Function.update s dst (b :: s dst)⟩ := by
  have he : (fun i => (if i = dst then Action.push b else Action.stay).apply (s i)) =
      Function.update s dst (b :: s dst) := by
    funext i
    by_cases hi : i = dst <;> simp [hi,Action.apply]
  simpa only [push,he] using instruction_exec (fun _ i => if i = dst then .push b else .stay) s

theorem setNil_runs (dst : Fin (k+1)) (s : Store k) :
    (setNil dst).Runs s (Function.update s dst Data.nil.encode) (3*(s dst).length+2) := by
  have h := (clear_exec dst s).runs.seq (push_exec dst false (Function.update s dst [])).runs
  simpa [setNil] using h

theorem setPair_runs {dst a b tmp buf : Fin (k+1)}
    (hd : dst ≠ tmp) (hd' : dst ≠ buf) (ha : a ≠ tmp) (ha' : a ≠ buf)
    (hb : b ≠ tmp) (hb' : b ≠ buf) (htb : tmp ≠ buf)
    (s : Store k) (ht : s tmp = []) (hu : s buf = []) :
    (setPair dst a b tmp buf).Runs s
      (Function.update s dst (true :: (s a ++ s b)))
      (12*(s a).length+12*(s b).length+3*(s dst).length+14) := by
  let s₁ := Function.update s tmp (s b)
  let s₂ := Function.update s tmp (s a ++ s b)
  let s₃ := Function.update s tmp (true :: (s a ++ s b))
  have h₁ : (prepend b tmp buf).Runs s s₁ (6*(s b).length+1) := by
    simpa [s₁,ht] using (prepend_exec hb hb' htb s hu).runs
  have h₂ : (prepend a tmp buf).Runs s₁ s₂ (6*(s a).length+1) := by
    have hh := (prepend_exec ha ha' htb s₁ (by simp [s₁,htb.symm,hu])).runs
    simpa [s₁,s₂,ha] using hh
  have h₃ : (push tmp true).Runs s₂ s₃ 1 := by
    simpa [s₂,s₃] using (push_exec tmp true s₂).runs
  have h₄ : (move tmp dst buf).Runs s₃ (Function.update s dst (true :: (s a ++ s b)))
      (3*(s dst).length+6*((s a).length+(s b).length+1)+2) := by
    have hh := (move_exec hd.symm htb hd' s₃ (by simp [s₃,htb.symm,hu])).runs
    have he : Function.update s₃ tmp [] = s := by
      ext i
      by_cases hi : i = tmp <;> simp [s₃,hi,ht]
    rw [he] at hh
    simpa [s₃,hd] using hh
  exact (h₁.seq (h₂.seq (h₃.seq h₄))).mono (by omega)

end ThreeMachine.StackCompiler.Program

end

end OAI
end

section
-- module RegisterMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

attribute [instance] Packed.finiteControl

namespace Packed
variable {k : ℕ}

theorem Runs.seq {P P' : Packed k} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (P.seq P').Runs s u (n+m+1) :=
  Program.Runs.seq h h'

theorem Runs.mono {P : Packed k} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := Program.Runs.mono h hnm

end Packed

namespace Tree
variable {r : ℕ}

theorem memory_update (s : Registers r) (dst : Fin r) (d : Data) :
    memory (Function.update s dst d) = Function.update (memory s) (reg dst) d.encode := by
  funext i
  refine Fin.addCases (m := r) (n := 4) (fun i => ?_) (fun i => ?_) i
  · change memory _ (reg i) = Function.update (memory s) (reg dst) d.encode (reg i)
    by_cases hi : i = dst <;> simp [hi]
  · change memory _ (temp i) = Function.update (memory s) (reg dst) d.encode (temp i)
    simp

theorem nil_runs (dst : Fin r) (s : Registers r) :
    (nil dst).Runs (memory s) (memory (Function.update s dst .nil)) (3*(s dst).size+2) := by
  rw [memory_update]
  simpa only [nil,Packed.Runs,Packed.ofProgram,memory_reg,Data.size] using Program.setNil_runs (reg dst) (memory s)

theorem pair_runs (dst a b : Fin r) (s : Registers r) :
    (pair dst a b).Runs (memory s) (memory (Function.update s dst (.pair (s a) (s b))))
      (12*(s a).size+12*(s b).size+3*(s dst).size+14) := by
  rw [memory_update]
  simpa only [pair,Packed.Runs,Packed.ofProgram,memory_reg,Data.size,Data.encode_pair,List.cons_append] using
    Program.setPair_runs (dst := reg dst) (a := reg a) (b := reg b) (tmp := temp 0) (buf := temp 1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (memory s) (by simp) (by simp)

end Tree
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem work_update_temp (s : Registers r) (t : Fin 4 → List Bool) (i : Fin 4) (word : List Bool) :
    Function.update (work s t) (temp i) word = work s (Function.update t i word) := by
  funext j
  refine Fin.addCases (m := r) (n := 4) (fun j => ?_) (fun j => ?_) j
  · change Function.update (work s t) (temp i) word (reg j) = work _ _ (reg j)
    simp
  · change Function.update (work s t) (temp i) word (temp j) = work _ _ (temp j)
    by_cases hj : j = i <;> simp [hj]

theorem selectFinish_runs (head : Bool) (s : Registers r) (a b : Data) :
    (selectFinish head).Runs (work s ![b.encode,[],a.encode.reverse,[]])
      (work s ![(if head then a else b).encode,[],[],[]]) (3*a.size+3*b.size+2) := by
  cases head with
  | false =>
    have h₁ := (Program.clear_exec (temp 2) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.clear_exec (temp 2) (work s ![b.encode,[],[],[]])).runs
    rw [work_update_temp] at h₂
    have he₂ : Function.update ![b.encode,[],[],[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    have hx := h₁.seq h₂
    exact hx.mono (by simp [Data.size]; omega)
  | true =>
    have h₁ := (Program.clear_exec (temp 0) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (0 : Fin 4) [] = ![[],[],a.encode.reverse,[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.transfer_exec (show (temp 2 : Fin (r+4)) ≠ temp 0 by simp)
      (work s ![[],[],a.encode.reverse,[]])).runs
    have he₂ : Program.transferResult (temp 2) (temp 0) (work s ![[],[],a.encode.reverse,[]]) =
        work s ![a.encode,[],[],[]] := by
      simp only [Program.transferResult,work_temp,Matrix.cons_val_two,Matrix.cons_val_zero,
        List.append_nil,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem selectPair_runs (head : Bool) (dst : Fin r) (s : Registers r) (a b : Data) :
    (selectPair head dst).Runs (work s ![(Data.pair a b).encode,[],[],[]])
      (memory (Function.update s dst (if head then a else b)))
      (30*(a.size+b.size+(s dst).size+1)) := by
  let s₀ := work s ![(Data.pair a b).encode,[],[],[]]
  let s₁ := work s ![a.encode++b.encode,[],[],[]]
  let s₂ := work s ![a.encode++b.encode,[],[],[true]]
  let s₃ := work s ![b.encode,[],a.encode.reverse,[]]
  let s₄ := work s ![(if head then a else b).encode,[],[],[]]
  have h₁ : (Packed.ofProgram (Program.instruction (fun _ => Program.popActions (temp 0)))).Runs s₀ s₁ 1 := by
    have hh := (Program.pop_instruction (temp 0) s₀).runs
    have he : Function.update s₀ (temp 0) (s₀ (temp 0)).tail = s₁ := by
      simp only [s₀,s₁,work_temp,Matrix.cons_val_zero,Data.encode_pair,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₂ : (Packed.ofProgram (Program.push (temp 3) true)).Runs s₁ s₂ 1 := by
    have hh := (Program.push_exec (temp 3) true s₁).runs
    have he : Function.update s₁ (temp 3) (true :: s₁ (temp 3)) = s₂ := by
      simp only [s₁,s₂,work_temp,Matrix.cons_val_three,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₃ : (Packed.ofProgram (Program.scan (temp 0) (temp 2) (temp 3))).Runs s₂ s₃ (3*a.size) := by
    have hh := (Program.scan_tree (src := temp 0) (dst := temp 2) (ct := temp 3)
      (by simp) (by simp) (by simp) a s₂ b.encode (by simp [s₂]) (by simp [s₂])).runs
    have he : Program.scanned (temp 0) (temp 2) (temp 3) s₂ b.encode a.encode 0 = s₃ := by
      simp only [Program.scanned,s₂,s₃,work_temp,Matrix.cons_val_two,
        List.replicate_zero,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₄ : (selectFinish head).Runs s₃ s₄ (3*a.size+3*b.size+2) :=
    selectFinish_runs head s a b
  have h₅ : (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1))).Runs s₄
      (memory (Function.update s dst (if head then a else b)))
      (3*(s dst).size+6*(if head then a else b).size+2) := by
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) s₄ (by simp [s₄])).runs
    have he : Function.update s₄ (temp 0) [] = memory s := by
      simp only [s₄,work_update_temp]
      have hw : Function.update ![(if head then a else b).encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    simpa only [Packed.Runs,Packed.ofProgram,s₄,work_reg,work_temp,Matrix.cons_val_zero,← memory_update,Data.size] using hh
  apply (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono
  cases head <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem selectAux_runs (head : Bool) (dst : Fin r) (s : Registers r) (d : Data) :
    (selectAux head dst).Runs (work s ![d.encode,[],[],[]])
      (memory (Function.update s dst (if head then d.head else d.tail)))
      (40*(d.size+(s dst).size+1)) := by
  cases d with
  | nil =>
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) (work s ![Data.nil.encode,[],[],[]]) (by simp)).runs
    have he : Function.update (work s ![Data.nil.encode,[],[],[]]) (temp 0) [] = memory s := by
      rw [work_update_temp]
      have hw : Function.update ![Data.nil.encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    have hx := hh.branch_right (fun h => (h (temp 0)).getD false) (selectPair head dst).program (by simp)
    have hout : (if head then Data.nil.head else Data.nil.tail) = Data.nil := by cases head <;> rfl
    rw [hout,memory_update]
    simpa only [selectAux,Packed.Runs,Packed.branch,Packed.ofProgram,work_temp,Matrix.cons_val_zero] using
      hx.mono (m := 40*(Data.nil.size+(s dst).size+1)) (by simp [Data.size]; omega)
  | pair a b =>
    have hh := selectPair_runs head dst s a b
    have hx := Program.Runs.branch_left (fun h => (h (temp 0)).getD false)
      (Program.move (temp 0) (reg dst) (temp 1)) hh (by simp [Data.encode_pair])
    exact hx.mono (by simp [Data.size_pair]; omega)

theorem select_runs (head : Bool) (dst src : Fin r) (s : Registers r) :
    (select head dst src).Runs (memory s)
      (memory (Function.update s dst (if head then (s src).head else (s src).tail)))
      (50*((s src).size+(s dst).size+1)) := by
  have h₁ := (Program.copy_exec (src := reg src) (dst := temp 0) (tmp := temp 1)
    (by simp) (by simp) (by simp) (memory s) (by simp)).runs
  have he : Function.update (memory s) (temp 0) (memory s (reg src)) = work s ![(s src).encode,[],[],[]] := by
    rw [memory_reg,← work_empty,work_update_temp]
    congr 1
    funext i; fin_cases i <;> simp
  rw [he] at h₁
  have h₂ := selectAux_runs head dst s (s src)
  exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q : Type}

theorem Runs.loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (hs : test (fun i => (s i).head?) = false) : (loop test P).Runs s s 0 :=
  (Program.loop_stop test P s hs).runs

theorem Runs.loop_iterate (test : Heads k → Bool) {P : Program k Q}
    {s t u : Store k} {n m : ℕ} (h : P.Runs s t n) (h' : (loop test P).Runs t u m)
    (hs : test (fun i => (s i).head?) = true) : (loop test P).Runs s u (n+m+2) := by
  obtain ⟨n',hn,q,hq⟩ := h
  obtain ⟨m',hm,r,hr⟩ := h'
  have hnone : r = none := by
    have hh := hr.halted
    cases r with
    | none => rfl
    | some q =>
      unfold step at hh
      cases he : P.transition q (fun i => (u i).head?) <;> simp_all [loop]
  subst r
  exact (Program.loop_iterate test hs hq hr).runs.mono (by omega)

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem skip_runs (s : Registers r) : skip.Runs (memory s) (memory s) 1 := by
  have hh := (Program.instruction_exec (k := r+3) (fun _ => Program.stayActions) (memory s)).runs
  simpa only [skip,Packed.Runs,Packed.ofProgram,Program.stayActions,Action.apply] using hh

theorem copy_runs (dst src : Fin r) (s : Registers r) :
    (copy dst src).Runs (memory s) (memory (Function.update s dst (s src)))
      (3*(s dst).size+6*(s src).size+2) := by
  by_cases he : dst = src
  · subst src
    simpa [copy] using (skip_runs s).mono (by omega : 1 ≤ 3*(s dst).size+6*(s dst).size+2)
  · rw [memory_update]
    unfold copy
    rw [ite_eq_right he]
    have hh := (Program.copy_exec (src := reg src) (dst := reg dst) (tmp := temp 0)
      (by simpa using Ne.symm he) (by simp) (by simp) (memory s) (by simp)).runs
    simpa only [memory_reg,Data.size,Packed.Runs,Packed.ofProgram] using hh

namespace Code

end Code

theorem Eval.compile {p : Code (Fin r)} {s t : Registers r} {n : ℕ} (h : Eval p s t n) :
    p.compile.Runs (memory s) (memory t) (150*n) := by
  induction h with
  | skip s => exact (skip_runs s).mono (by omega)
  | nil dst s =>
    apply (nil_runs dst s).mono
    omega
  | pair dst a b s =>
    apply (pair_runs dst a b s).mono
    omega
  | select head dst src s =>
    apply (select_runs head dst src s).mono
    omega
  | copy dst src s =>
    apply (copy_runs dst src s).mono
    omega
  | seq _ _ ih ih' => exact (ih.seq ih').mono (by omega)
  | @branch_true src p q s t n hs _ ih =>
    exact (Program.Runs.branch_left _ q.compile.program ih (by simpa using hs)).mono (by omega)
  | @branch_false src p q s t n hs _ ih =>
    exact (Program.Runs.branch_right _ p.compile.program ih (by simpa using hs)).mono (by omega)
  | @loop_stop src p s hs =>
    exact (Program.Runs.loop_stop _ p.compile.program (memory s) (by simpa using hs)).mono (by omega)
  | @loop_step src p s t u n m hs _ _ ih ih' =>
    exact (Program.Runs.loop_iterate _ ih ih' (by simpa using hs)).mono (by omega)

end ThreeMachine.StackCompiler.Tree

end

end OAI
end

section
-- module RoutineCompiler
namespace OAI

section

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_of_agree (f : V → W) (s : V → Data) (base : W → Data)
    (h : ∀ i, base (f i) = s i) : overlay f s base = base := by
  funext j
  by_cases hj : ∃ a, f a = j
  · unfold overlay Function.extend
    simp only [dite_eq_left hj]
    rw [← h]
    congr 1
    exact Classical.choose_spec hj
  · exact overlay_out s base hj

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

attribute [instance] Routine.finiteVars Routine.decVars

namespace Routine
variable {f g : Data → Data} {charge charge' : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

variable {V : Type} [DecidableEq V]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]

end ThreeMachine.StackCompiler.Tree

end

end OAI
end

section
-- module MachineBridge
namespace OAI

section

namespace ThreeMachine.StackCompiler.Packed
variable {k : ℕ}

theorem halt_runs (s : Store k) : halt.Runs s s 0 :=
  ⟨0,le_rfl,(),Program.Exec.halt rfl⟩

theorem pushWord_runs (dst : Fin (k+1)) (bs : List Bool) (s : Store k) :
    (pushWord dst bs).Runs s (Function.update s dst (bs ++ s dst)) (2*bs.length) := by
  induction bs with
  | nil => simpa only [pushWord,List.nil_append,Function.update_eq_self,List.length_nil,Nat.mul_zero] using halt_runs s
  | cons b bs ih =>
    have hp : (ofProgram (Program.push dst b)).Runs (Function.update s dst (bs ++ s dst))
        (Function.update (Function.update s dst (bs ++ s dst)) dst (b :: (bs ++ s dst))) 1 := by
      change (Program.push dst b).Runs _ _ _
      simpa only [Function.update_self] using (Program.push_exec dst b (Function.update s dst (bs ++ s dst))).runs
    have h := ih.seq hp
    simpa only [pushWord,List.length_cons,Function.update_self,Function.update_idem,
      List.cons_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h

theorem pop_runs (src : Fin (k+1)) (s : Store k) :
    (pop src).Runs s (Function.update s src (s src).tail) 1 :=
  (Program.pop_instruction src s).runs

theorem popN_runs (src : Fin (k+1)) (n : ℕ) (s : Store k) :
    (popN src n).Runs s (Function.update s src ((s src).drop n)) (2*n) := by
  induction n generalizing s with
  | zero => simpa only [popN,List.drop_zero,Function.update_eq_self,Nat.mul_zero] using halt_runs s
  | succ n ih =>
    have h := (pop_runs src s).seq (ih (Function.update s src (s src).tail))
    have h' := h.mono (show 1+2*n+1 ≤ 2*(n+1) by omega)
    simpa only [popN,Function.update_self,Function.update_idem,List.drop_tail] using h'

end ThreeMachine.StackCompiler.Packed

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

theorem encoded_cons (b : Bool) (xs : List Bool) :
    (enc (b :: xs)).encode = boolChunk b ++ (enc xs).encode := rfl

theorem encodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = b :: bs) :
    (encodeBody src dst).Runs s
      (Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)) 12 := by
  have h := (Packed.pop_runs src s).seq
    (Packed.pushWord_runs dst (boolChunk b) (Function.update s src (s src).tail))
  simp only [hs,List.tail_cons,Function.update_of_ne hne.symm] at h
  cases b with
  | false =>
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by decide)
  | true =>
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by decide)

theorem encodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs ys : List Bool) (s : Store k) (hs : s src = bs) (hd : s dst = (enc ys).encode) :
    (encodeLoop src dst).Runs s
      (Function.update (Function.update s src []) dst (enc (bs.reverse ++ ys)).encode)
      (14*bs.length) := by
  induction bs generalizing ys s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (enc ([] ++ ys)).encode = s := by
      rw [List.nil_append,← hd]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by simp [hs])
  | cons b bs ih =>
    let t := Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)
    have hb : (encodeBody src dst).Runs s t 12 := encodeBody_runs hne b bs s hs
    have ht : t src = bs := by simp [t,hne]
    have hd' : t dst = (enc (b :: ys)).encode := by simp only [t,Function.update_self,hd,encoded_cons]
    have hr := ih (b :: ys) t ht hd'
    have he : Function.update (Function.update t src []) dst (enc (bs.reverse ++ b :: ys)).encode =
        Function.update (Function.update s src []) dst (enc ((b :: bs).reverse ++ ys)).encode := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by simp [hs])).mono (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

theorem decodeAfterTag_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (rest : List Bool) (s : Store k) (hs : s src = (enc b).encode ++ rest) :
    (decodeAfterTag src dst).Runs s
      (Function.update (Function.update s src rest) dst (b :: s dst)) 10 := by
  cases b with
  | false =>
    have h := Program.Runs.seq (Packed.popN_runs src 1 s)
      (Program.push_exec dst false (Function.update s src ((s src).drop 1))).runs
    have he : (enc false).encode = [false] := rfl
    simp only [hs,he,List.singleton_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by omega)
  | true =>
    have h := Program.Runs.seq (Packed.popN_runs src 3 s)
      (Program.push_exec dst true (Function.update s src ((s src).drop 3))).runs
    have he : (enc true).encode = [true,false,false] := rfl
    simp only [hs,he,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by omega)

theorem decodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = (enc (b :: bs)).encode) :
    (decodeBody src dst).Runs s
      (Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)) 12 := by
  have ht : (Function.update s src (s src).tail) src = (enc b).encode ++ (enc bs).encode := by
    simp only [Function.update_self,hs,encoded_cons,boolChunk,List.cons_append,List.tail_cons]
  have h := (Packed.pop_runs src s).seq (decodeAfterTag_runs hne b (enc bs).encode _ ht)
  simpa only [decodeBody,Function.update_idem,Function.update_of_ne hne.symm,Nat.reduceAdd] using h

theorem decodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs : List Bool) (s : Store k) (hs : s src = (enc bs).encode) :
    (decodeLoop src dst).Runs s
      (Function.update (Function.update s src [false]) dst (bs.reverse ++ s dst))
      (14*bs.length) := by
  induction bs generalizing s with
  | nil =>
    have he : Function.update (Function.update s src [false]) dst ([] ++ s dst) = s := by
      rw [List.nil_append]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by change (s src).head?.getD false = _; rw [hs]; rfl)
  | cons b bs ih =>
    let t := Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)
    have hb : (decodeBody src dst).Runs s t 12 := decodeBody_runs hne b bs s hs
    have hr := ih t (by simp [t,hne])
    have he : Function.update (Function.update t src [false]) dst (bs.reverse ++ t dst) =
        Function.update (Function.update s src [false]) dst ((b :: bs).reverse ++ s dst) := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by change (s src).head?.getD false = _; rw [hs]; rfl)).mono
      (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_zero (f : V → W) : overlay f (zeroStore V) (zeroStore W) = zeroStore W :=
  overlay_of_agree f _ _ (fun _ => rfl)

theorem overlay_start {f : V → W} (hf : Function.Injective f) (input : V) (x : Data) :
    overlay f (start input x) (zeroStore W) = start (f input) x := by
  rw [start,overlay_update hf,overlay_zero]
  rfl

theorem overlay_finish {f : V → W} (hf : Function.Injective f) (a b : V) (x y : Data) :
    overlay f (finish a b x y) (zeroStore W) = finish (f a) (f b) x y := by
  rw [finish,overlay_update hf,overlay_start hf]
  rfl

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Routine
open ThreeMachine.StackCompiler.Tree
variable {f : Data → Data} {charge : Data → ℕ}
variable (R : Routine f charge)

theorem number_injective : Function.Injective R.number :=
  (Fin.succ_injective _).comp (Fintype.equivFin R.Vars).injective

theorem numberedCode_runs (x : Data) :
    R.numberedCode.compile.Runs (memory (start (R.number R.input) x))
      (memory (finish (R.number R.input) (R.number R.output) x (f x))) (150*charge x) := by
  obtain ⟨n,hn,he⟩ := R.correct x
  have hh := (he.rename R.number_injective (zeroStore (Fin (Fintype.card R.Vars+1)))).compile
  rw [overlay_start R.number_injective,overlay_finish R.number_injective] at hh
  exact hh.mono (Nat.mul_le_mul_left 150 hn)

theorem initRegs_runs (s : Store (Fintype.card R.Vars+4)) :
    R.initRegs.Runs s (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) 1 := by
  have he : (fun j => (if j.val < Fintype.card R.Vars+1 then Action.push false else Action.stay).apply (s j)) =
      (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) := by
    funext j
    split_ifs <;> rfl
  simpa only [initRegs,Packed.Runs,Packed.ofProgram,he] using
    (Program.instruction_exec (fun _ j =>
      if j.val < Fintype.card R.Vars+1 then Action.push false else .stay) s).runs

theorem inputProgram_runs (bs : List Bool) :
    R.inputProgram.Runs (initialStore bs)
      (memory (start (R.number R.input) (enc bs))) (17*bs.length+3) := by
  let s : Store (Fintype.card R.Vars+4) := Function.update (fun _ => []) (temp 0) bs.reverse
  have ht : (Packed.ofProgram (Program.transfer 0 (temp 0))).Runs
      (initialStore bs) s (3*bs.length) := by
    have h := (Program.transfer_exec (Ne.symm R.temp_ne_zero) (initialStore bs)).runs
    have he : Program.transferResult 0 (temp 0) (initialStore bs) = s := by
      funext i
      by_cases hi : i = temp 0 <;> by_cases hz : i = 0 <;>
        simp_all [Program.transferResult,initialStore,s,R.temp_ne_zero,Ne.symm R.temp_ne_zero]
    simpa only [Packed.Runs,Packed.ofProgram,initialStore,ite_true,he] using h
  let t : Store (Fintype.card R.Vars+4) :=
    fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j
  have hi : R.initRegs.Runs s t 1 := R.initRegs_runs s
  have hts : t (temp 0) = bs.reverse := by simp [t,s,temp]
  have htd : t (reg (R.number R.input)) = (enc ([] : List Bool)).encode := by
    have hv : (reg (R.number R.input)).val < Fintype.card R.Vars+1 := (R.number R.input).isLt
    simp only [t,ite_eq_left hv,s,Function.update_of_ne (reg_ne_temp _ _)]
    rfl
  have he := Raw.encodeLoop_runs (temp_ne_reg _ _) bs.reverse [] t hts htd
  have hfinal : Function.update (Function.update t (temp 0) [])
      (reg (R.number R.input)) (enc (bs.reverse.reverse ++ [])).encode =
      memory (start (R.number R.input) (enc bs)) := by
    simp only [List.reverse_reverse,List.append_nil]
    funext j
    refine Fin.addCases (m := Fintype.card R.Vars+1) (n := 4) (fun i => ?_) (fun i => ?_) j
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (reg i) = memory (start (R.number R.input) (enc bs)) (reg i)
      by_cases hh : i = R.number R.input
      · subst i; simp
      · have hv : (reg i).val < Fintype.card R.Vars+1 := i.isLt
        simp only [Function.update_of_ne (show reg i ≠ reg (R.number R.input) by simpa using hh),
          memory_reg,start_other _ hh,t,ite_eq_left hv,s,
          Function.update_of_ne (reg_ne_temp _ _)]
        rfl
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (temp i) = memory (start (R.number R.input) (enc bs)) (temp i)
      by_cases hh : i = 0
      · subst i; simp
      · have hv : ¬(temp (r := Fintype.card R.Vars+1) i).val < Fintype.card R.Vars+1 := by
          simp only [temp,Fin.val_natAdd]; omega
        simp only [Function.update_of_ne (temp_ne_reg _ _),memory_temp,
          Function.update_of_ne (show (temp i : Fin (Fintype.card R.Vars+1+4)) ≠ temp 0 by simpa using hh),
          t,ite_eq_right hv,s]
  rw [hfinal] at he
  exact (ht.seq (hi.seq he)).mono (by simp only [List.length_reverse]; omega)

theorem outputProgram_runs (bs out : List Bool) :
    ∃ t, R.outputProgram.Runs
      (memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))) t
      (17*out.length+3) ∧ t 0 = out := by
  let s := memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))
  have hzero : s 0 = [false] := by
    change memory _ (reg (0 : Fin (Fintype.card R.Vars+1))) = _
    simp only [memory_reg,finish,Function.update_of_ne (Ne.symm (R.number_ne_zero R.output)),
      start_other _ (Ne.symm (R.number_ne_zero R.input))]
    rfl
  have hd := Raw.decodeLoop_runs (reg_ne_temp _ 0) out s
    (show s (reg (R.number R.output)) = (enc out).encode by simp [s])
  let u := Function.update (Function.update s (reg (R.number R.output)) [false])
    (temp 0) (out.reverse ++ s (temp 0))
  have hu : u 0 = [false] := by
    simp only [u,Function.update_of_ne (Ne.symm R.temp_ne_zero),
      Function.update_of_ne (Ne.symm (R.reg_number_ne_zero R.output)),hzero]
  have hv : u (temp 0) = out.reverse := by simp [u,s]
  let v := Function.update u 0 []
  have hp : (Packed.pop 0).Runs u v 1 := by
    simpa only [hu,List.tail_cons,List.tail_nil] using Packed.pop_runs 0 u
  have ht := (Program.transfer_exec R.temp_ne_zero v).runs
  have hvt : v (temp 0) = out.reverse := by simp [v,R.temp_ne_zero,hv]
  have hvz : v 0 = [] := by simp [v]
  rw [hvt,List.length_reverse] at ht
  have ht' : (Packed.ofProgram (Program.transfer (temp 0) 0)).Runs v
      (Program.transferResult (temp 0) 0 v) (3*out.length) := ht
  refine ⟨Program.transferResult (temp 0) 0 v,?_,?_⟩
  · exact (hd.seq (hp.seq ht')).mono (by omega)
  · simp [Program.transferResult,hvt,hvz]

theorem rawProgram_runs (bs out : List Bool) (h : f (enc bs) = enc out) :
    ∃ t, R.rawProgram.Runs (initialStore bs) t
      (1000*(charge (enc bs)+bs.length+out.length+1)) ∧ t 0 = out := by
  have hi := R.inputProgram_runs bs
  have hc := R.numberedCode_runs (enc bs)
  rw [h] at hc
  obtain ⟨t,ho,ht⟩ := R.outputProgram_runs bs out
  exact ⟨t,(hi.seq (hc.seq ho)).mono (by omega),ht⟩

include R in
theorem exists_rawMachine : ∃ k q g, ∃ M : Machine k q g,
    ∀ bs out, f (enc bs) = enc out →
      M.Produces bs out (2000*(charge (enc bs)+bs.length+out.length+1)) := by
  refine ⟨_,_,_,compile R.rawProgram.program,?_⟩
  intro bs out h
  obtain ⟨t,ht,ho⟩ := R.rawProgram_runs bs out h
  have hh := ht.computes
  obtain ⟨n,hn,hs,hh⟩ := hh
  have he := compile_produces R.rawProgram.program bs out
    (1000*(charge (enc bs)+bs.length+out.length+1)) ⟨n,hn,hh,by rw [hs,ho]⟩
  simpa only [← Nat.mul_assoc] using he

end ThreeMachine.StackCompiler.Routine
end

end OAI
end

end

-- Solutions.RawStackTrace
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kDecidableEq
open Turing.TM2
variable {κ Λ σ : Type} [DecidableEq κ] {Γ : κ → Type}

 def cfg (l : Option Λ) (v : σ) (S : ∀i,List (Γ i)) : Cfg Γ Λ σ := ⟨l,v,S⟩
 def run (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : ℕ → Option (Cfg Γ Λ σ)
   | 0 => some c
   | t+1 => (run code c t).bind (step code)

 theorem run_iter (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) :
    run code c t=(fun o : Option (Cfg Γ Λ σ) => o.bind (step code))^[t] (some c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run,ih,Function.iterate_succ_apply']

 theorem run_add (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (s t : ℕ) :
    run code c (s+t)=(run code c s).bind (fun d => run code d t) := by
  induction t with
  | zero => simp only [Nat.add_zero,run]; cases run code c s <;> rfl
  | succ t ih => rw [Nat.add_succ,run,ih]; simp only [Option.bind_assoc,run]

 theorem run_trans (code : Λ → Stmt Γ Λ σ) (c d e : Cfg Γ Λ σ) (s t : ℕ)
    (hs : run code c s=some d) (ht : run code d t=some e) : run code c (s+t)=some e := by
  rw [run_add,hs,Option.bind_some,ht]

 theorem run_one (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : run code c 1=step code c := rfl

 theorem run_first (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) :
    run code c (t+1)=(step code c).bind (fun d => run code d t) := by
  rw [show t+1=1+t by omega,run_add,run_one]

 theorem outputs {tm : Turing.FinTM2} (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    (t : ℕ) (h : run tm.m (Turing.initList tm input) t=some (Turing.haltList tm output)) :
    Nonempty (Turing.TM2OutputsInTime tm input (some output) t) := by
  refine ⟨⟨⟨t,?_⟩,le_rfl⟩⟩
  have h' := run_iter tm.m (Turing.initList tm input) t
  rw [h'] at h
  exact h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.TreeToTM2
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open Turing.TM2
variable {κ Λ : Type} [DecidableEq κ]
abbrev Heads (κ : Type) := κ → Option Bool
abbrev StmtB (κ Λ : Type) := Stmt (fun _ : κ => Bool) Λ (Heads κ)

 def readHeads : List κ → StmtB κ Λ → StmtB κ Λ
   | [],next => next
   | i::L,next => .peek i (fun h b => Function.update h i b) (readHeads L next)

 theorem readHeads_aux (L : List κ) (next : StmtB κ Λ) (h : Heads κ) (S : κ → List Bool) :
    stepAux (readHeads L next) h S = stepAux next (fun i => if i∈L then (S i).head? else h i) S := by
  induction L generalizing h with
  | nil => simp [readHeads]
  | cons i L ih =>
    simp only [readHeads,stepAux,ih]
    congr 1
    funext j
    by_cases hj : j=i <;> by_cases hm : j∈L <;> simp [hj,hm]

 def actionCode (i : κ) (a : Heads κ → OAI.ThreeMachine.StackCompiler.Action) (next : StmtB κ Λ) : StmtB κ Λ :=
   .branch (fun h => match a h with | .stay => true | _ => false) next
     (.branch (fun h => match a h with | .pop => true | _ => false)
       (.pop i (fun h _ => h) next)
       (.push i (fun h => match a h with | .push b => b | _ => false) next))

 theorem actionCode_aux (i : κ) (a : Heads κ → OAI.ThreeMachine.StackCompiler.Action) (next : StmtB κ Λ)
    (h : Heads κ) (S : κ → List Bool) :
    stepAux (actionCode i a next) h S=stepAux next h (Function.update S i ((a h).apply (S i))) := by
  unfold actionCode
  cases he : a h <;> simp [stepAux,he,OAI.ThreeMachine.StackCompiler.Action.apply]

 def actionsCode : List κ → (Heads κ → κ → OAI.ThreeMachine.StackCompiler.Action) → StmtB κ Λ → StmtB κ Λ
   | [],_,next => next
   | i::L,a,next => actionCode i (fun h => a h i) (actionsCode L a next)

 theorem actionsCode_aux (L : List κ) (hL : L.Nodup) (a : Heads κ → κ → OAI.ThreeMachine.StackCompiler.Action)
    (next : StmtB κ Λ) (h : Heads κ) (S : κ → List Bool) :
    stepAux (actionsCode L a next) h S =
      stepAux next h (fun i => if i∈L then (a h i).apply (S i) else S i) := by
  induction L generalizing S with
  | nil => simp [actionsCode]
  | cons i L ih =>
    rw [actionsCode,actionCode_aux,ih (List.nodup_cons.mp hL).2]
    congr 1
    funext j
    by_cases hj : j=i
    · subst j
      simp [(List.nodup_cons.mp hL).1]
    · simp [hj]

variable {k : ℕ} {Q : Type} [Fintype Q]
abbrev Label (k : ℕ) (Q : Type) := Q ⊕ Fin (k+2)

 def defaultActions (h : Heads (Fin (k+1))) : Fin (k+1) → OAI.ThreeMachine.StackCompiler.Action := fun _ => .stay
 def choice (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q : Q) (h : Heads (Fin (k+1))) : Q × OAI.ThreeMachine.StackCompiler.Actions k :=
   (P.transition q h).getD (q,fun _ => .stay)

 def source (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q : Q) : StmtB (Fin (k+1)) (Label k Q) :=
   readHeads (List.finRange (k+1))
     (.branch (fun h => (P.transition q h).isSome)
       (actionsCode (List.finRange (k+1)) (fun h => (choice P q h).2)
         (.goto (fun h => .inl (choice P q h).1)))
       (.goto (fun _ => .inr 0)))

 theorem source_some (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q q' : Q) (a : OAI.ThreeMachine.StackCompiler.Actions k)
    (h : Heads (Fin (k+1))) (S : OAI.ThreeMachine.StackCompiler.Store k)
    (he : P.transition q (fun i => (S i).head?)=some (q',a)) :
    stepAux (source P q) h S=⟨some (.inl q'),(fun i => (S i).head?),fun i => (a i).apply (S i)⟩ := by
  rw [source,readHeads_aux]
  simp only [List.mem_finRange,ite_true]
  simp only [stepAux,he,Option.isSome_some,cond_true]
  rw [actionsCode_aux _ (List.nodup_finRange _)]
  simp only [List.mem_finRange,ite_true,stepAux,choice,he,Option.getD_some]

 theorem source_none (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q : Q) (h : Heads (Fin (k+1))) (S : OAI.ThreeMachine.StackCompiler.Store k)
    (he : P.transition q (fun i => (S i).head?)=none) :
    stepAux (source P q) h S=⟨some (.inr 0),(fun i => (S i).head?),S⟩ := by
  rw [source,readHeads_aux]
  simp only [List.mem_finRange,ite_true,stepAux,he,Option.isSome_none,cond_false]

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.TreeTM2Cleanup
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
variable {k : ℕ} {Q : Type}

 def clearStmt (j : Fin (k+2)) : StmtB (Fin (k+1)) (Label k Q) :=
   if hj : j.val< k+1 then
     if j.val=0 then .goto (fun _ => .inr ⟨j.val+1,by omega⟩)
     else let i : Fin (k+1) := ⟨j.val,hj⟩
       .pop i (fun h b => Function.update h i b)
         (.branch (fun h => (h i).isSome) (.goto (fun _ => .inr j))
           (.goto (fun _ => .inr ⟨j.val+1,by omega⟩)))
   else .load (fun _ => fun _ => none) .halt

 def code (P : OAI.ThreeMachine.StackCompiler.Program k Q) : Label k Q → StmtB (Fin (k+1)) (Label k Q)
   | .inl q => source P q
   | .inr j => clearStmt j

 theorem clear_stack (P : OAI.ThreeMachine.StackCompiler.Program k Q) (j : Fin (k+2))
    (hj : j.val< k+1) (hj0 : j.val≠0) (S : Fin (k+1) → List Bool) (h : Heads (Fin (k+1)))
    (L : List Bool) (hs : S ⟨j.val,hj⟩=L) :
    run (code P) (cfg (some (.inr j)) h S) (L.length+1)=
      some (cfg (some (.inr ⟨j.val+1,by omega⟩))
        (Function.update h ⟨j.val,hj⟩ none) (Function.update S ⟨j.val,hj⟩ [])) := by
  let i : Fin (k+1) := ⟨j.val,hj⟩
  induction L generalizing h S with
  | nil =>
    rw [List.length_nil,zero_add,run_one]
    simp [step,cfg,code,clearStmt,hj,hj0,stepAux,hs]
  | cons b L ih =>
    have hstep : step (code P) (cfg (some (.inr j)) h S)=
        some (cfg (some (.inr j)) (Function.update h i (some b)) (Function.update S i L)) := by
      simp [step,cfg,code,clearStmt,hj,hj0,stepAux,hs,i]
    have hs' : Function.update S i L i=L := Function.update_self _ _ _
    rw [List.length_cons,run_first,hstep,Option.bind_some]
    have hh := ih (Function.update S i L) (Function.update h i (some b)) hs'
    simpa only [i,Function.update_idem] using hh

 def remaining (j : ℕ) (S : Fin (k+1) → List Bool) : ℕ :=
   ∑ i : Fin (k+1),if j ≤ i.val ∧ i.val≠0 then (S i).length else 0
 def cleaned (j : ℕ) (S : Fin (k+1) → List Bool) : Fin (k+1) → List Bool :=
   fun i => if i.val< j ∨ i.val=0 then S i else []

 theorem remaining_zero (S : Fin (k+1) → List Bool) : remaining 0 S=remaining 1 S := by
   unfold remaining
   apply Finset.sum_congr rfl
   intro i hi
   by_cases h0 : i.val=0 <;> simp [h0] <;> omega

 theorem remaining_step (j : ℕ) (hj : j< k+1) (hj0 : j≠0) (S : Fin (k+1) → List Bool) :
    remaining j S=(S ⟨j,hj⟩).length+remaining (j+1) (Function.update S ⟨j,hj⟩ []) := by
   let i : Fin (k+1) := ⟨j,hj⟩
   have hp : ∀ x : Fin (k+1),
       (if j≤ x.val ∧ x.val≠0 then (S x).length else 0)=
       (if x=i then (S i).length else 0)+
       (if j+1≤ x.val ∧ x.val≠0 then ((Function.update S i []) x).length else 0) := by
     intro x
     by_cases he : x=i
     · subst x; simp [i,hj0]
     · have hval : x.val≠j := by intro h; apply he; exact Fin.ext h
       by_cases hlo : j≤ x.val
       · have hnext : j+1≤ x.val := by omega
         simp [hlo,hnext,he,show x.val≠0 by omega]
       · have hn : ¬j+1≤ x.val := by omega
         simp [hlo,hn,he]
   unfold remaining
   simp_rw [hp,Finset.sum_add_distrib]
   simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
   rfl



 theorem clear_run (P : OAI.ThreeMachine.StackCompiler.Program k Q) (j : Fin (k+2))
    (S : Fin (k+1) → List Bool) (h : Heads (Fin (k+1))) :
    ∃ t,t≤ remaining j.val S+2*(k+2-j.val) ∧
      run (code P) (cfg (some (.inr j)) h S) t=
        some (cfg none (fun _ => none) (cleaned j.val S)) := by
  induction hm : k+1-j.val using Nat.strong_induction_on generalizing j S h with
  | h z ih =>
    by_cases hlast : j.val=k+1
    · refine ⟨1,by omega,?_⟩
      rw [run_one]
      have hn : ¬j.val< k+1 := by omega
      simp only [step,cfg,code,clearStmt,dif_neg hn,stepAux]
      congr 2
      funext i
      simp [cleaned,show i.val< j.val by omega]
    · have hj : j.val< k+1 := by have := j.isLt; omega
      let j' : Fin (k+2) := ⟨j.val+1,by omega⟩
      have hj' : k+1-j'.val< z := by dsimp [j']; omega
      by_cases hj0 : j.val=0
      · obtain ⟨t,ht,hr⟩ := ih (k+1-j'.val) hj' j' S h rfl
        have hs : step (code P) (cfg (some (.inr j)) h S)=some (cfg (some (.inr j')) h S) := by
          simp [step,cfg,code,clearStmt,hj,hj0,j']
        refine ⟨t+1,?_,?_⟩
        · have he : remaining j.val S=remaining j'.val S := by simpa [hj0,j'] using remaining_zero S
          rw [he]
          dsimp [j'] at ht ⊢
          omega
        · rw [run_first,hs,Option.bind_some,hr]
          congr 2
          funext i
          simp only [cleaned]
          have he : (i.val< j'.val ∨ i.val=0) ↔ (i.val< j.val ∨ i.val=0) := by dsimp [j']; omega
          simp only [he]
      · let i : Fin (k+1) := ⟨j.val,hj⟩
        let S' := Function.update S i []
        let h' := Function.update h i none
        obtain ⟨t,ht,hr⟩ := ih (k+1-j'.val) hj' j' S' h' rfl
        have hs := clear_stack P j hj hj0 S h (S i) rfl
        have ht' : (S i).length+1+t ≤ remaining j.val S+2*(k+2-j.val) := by
          rw [remaining_step j.val hj hj0 S]
          dsimp [j',S',i] at ht ⊢
          omega
        refine ⟨(S i).length+1+t,ht',?_⟩
        have hh := run_trans (code P) _ _ _ ((S i).length+1) t hs hr
        convert hh using 1
        congr 2
        funext x
        by_cases hxi : x=i
        · subst x
          simp [cleaned,S',i,hj0,j']
        · have hval : x.val≠j.val := by intro he; apply hxi; exact Fin.ext he
          have he : (x.val< j'.val ∨ x.val=0) ↔ (x.val< j.val ∨ x.val=0) := by dsimp [j']; omega
          simp only [cleaned,he,S',Function.update_of_ne hxi]

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.TreeTM2Execution
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
variable {k : ℕ} {Q : Type} [Fintype Q]

 theorem step_some (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (s t : OAI.ThreeMachine.StackCompiler.State k Q)
    (hs : P.step s=some t) (h : Heads (Fin (k+1))) :
    step (code P) (cfg (some (.inl s.control)) h s.store)=
      some (cfg (some (.inl t.control)) (fun i => (s.store i).head?) t.store) := by
  cases he : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [OAI.ThreeMachine.StackCompiler.Program.step,he] at hs
  | some qa =>
    have ht : t=⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [OAI.ThreeMachine.StackCompiler.Program.step,he] using hs.symm
    rw [ht]
    change some (stepAux (source P s.control) h s.store)=_
    rw [source_some P s.control qa.1 qa.2 h s.store he]
    rfl

 theorem exec_run (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    {s t : OAI.ThreeMachine.StackCompiler.State k Q} {n : ℕ}
    (he : P.Exec s n t) (h : Heads (Fin (k+1))) :
    ∃ h',run (code P) (cfg (some (.inl s.control)) h s.store) n=
      some (cfg (some (.inl t.control)) h' t.store) := by
  induction he generalizing h with
  | halt hh => exact ⟨h,rfl⟩
  | @next s t u n hs he ih =>
    obtain ⟨h',hr⟩ := ih (fun i => (s.store i).head?)
    refine ⟨h',?_⟩
    rw [run_first,step_some P s t hs h,Option.bind_some]
    exact hr

 def size (S : Fin (k+1) → List Bool) : ℕ := ∑ i,(S i).length

 theorem action_size (a : OAI.ThreeMachine.StackCompiler.Action) (L : List Bool) :
    (a.apply L).length  ≤  L.length+1 := by
  cases a <;> simp [OAI.ThreeMachine.StackCompiler.Action.apply] <;> omega

 theorem step_size (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (s t : OAI.ThreeMachine.StackCompiler.State k Q) (hs : P.step s=some t) :
    size t.store  ≤  size s.store+(k+1) := by
  cases he : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [OAI.ThreeMachine.StackCompiler.Program.step,he] at hs
  | some qa =>
    have ht : t=⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [OAI.ThreeMachine.StackCompiler.Program.step,he] using hs.symm
    rw [ht]
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (k+1)))) => action_size (qa.2 i) (s.store i))
    simpa [size,Finset.sum_add_distrib] using hh

 theorem exec_size (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    {s t : OAI.ThreeMachine.StackCompiler.State k Q} {n : ℕ} (he : P.Exec s n t) :
    size t.store  ≤  size s.store+(k+1)*n := by
  induction he with
  | halt hh => simp
  | @next s t u n hs he ih =>
    have hh := step_size P s t hs
    nlinarith

 theorem halt_none (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (s : OAI.ThreeMachine.StackCompiler.State k Q) (hs : P.step s=none) :
    P.transition s.control (fun i => (s.store i).head?)=none := by
  cases he : P.transition s.control (fun i => (s.store i).head?) with
  | none => rfl
  | some qa => simp [OAI.ThreeMachine.StackCompiler.Program.step,he] at hs

 theorem full_run (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    {s t : OAI.ThreeMachine.StackCompiler.State k Q} {n : ℕ} (he : P.Exec s n t)
    (h : Heads (Fin (k+1))) :
    ∃ m,m ≤ size s.store+(k+2)*n+2*k+5 ∧
      run (code P) (cfg (some (.inl s.control)) h s.store) m=
        some (cfg none (fun _ => none) (fun i => if i=0 then t.store 0 else [])) := by
  obtain ⟨h',hr⟩ := exec_run P he h
  have hn := halt_none P t he.halted
  have hs : step (code P) (cfg (some (.inl t.control)) h' t.store)=
      some (cfg (some (.inr 0)) (fun i => (t.store i).head?) t.store) := by
    change some (stepAux (source P t.control) h' t.store)=_
    rw [source_none P t.control h' t.store hn]
    rfl
  obtain ⟨m,hm,hclear⟩ := clear_run P 0 t.store (fun i => (t.store i).head?)
  have hremaining : remaining 0 t.store  ≤  size t.store := by
    unfold remaining size
    apply Finset.sum_le_sum
    intro i hi
    split_ifs <;> omega
  have hsize := exec_size P he
  refine ⟨n+1+m,by dsimp at hm; nlinarith,?_⟩
  have h1 := run_trans (code P) _ _ _ n 1 hr (by rw [run_one]; exact hs)
  have h2 := run_trans (code P) _ _ _ (n+1) m h1 hclear
  convert h2 using 1
  congr 2
  funext i
  by_cases hi : i=0
  · subst i; simp [cleaned]
  · have hiv : i.val ≠ 0 := by intro hh; apply hi; exact Fin.ext hh
    simp [cleaned,hi,hiv]

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.TreeTM2Program
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open EdgeSublinearMWIS.Main.RawStack
variable {k : ℕ} {Q : Type} [Fintype Q]

 def tm (P : OAI.ThreeMachine.StackCompiler.Program k Q) : Turing.FinTM2 where
   K := Fin (k+1)
   k₀ := 0
   k₁ := 0
   Γ := fun _ => Bool
   Λ := Label k Q
   main := .inl P.initial
   σ := Heads (Fin (k+1))
   initialState := fun _ => none
   m := code P

 def program (P : OAI.ThreeMachine.StackCompiler.Program k Q) : Program where
   machine := ⟨tm P,Equiv.refl _,Equiv.refl _⟩
   finiteAlphabet _ := by change Finite Bool; infer_instance

 theorem program_runs (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (input output : List Bool) (T : ℕ)
    (he : ∃ S,P.Runs (OAI.ThreeMachine.StackCompiler.initialStore input) S T ∧ S 0=output) :
    Runs (program P) input output (input.length+(k+2)*T+2*k+5) := by
   obtain ⟨S,hRun,hout⟩ := he
   obtain ⟨n,hn,q,hExec⟩ := hRun
   have hsize : size (OAI.ThreeMachine.StackCompiler.initialStore (k:=k) input)=input.length := by
     unfold size OAI.ThreeMachine.StackCompiler.initialStore
     simp_rw [apply_ite,List.length_nil]
     simp
   obtain ⟨m,hm,hr⟩ := full_run P hExec (fun _ => none)
   rw [hsize] at hm
   have hstart : Turing.initList (tm P) input=cfg (some (.inl P.initial)) (fun _ => none)
       (OAI.ThreeMachine.StackCompiler.initialStore input) := by
     rfl
   have hfinish : Turing.haltList (tm P) output=cfg none (fun _ => none)
       (fun i : Fin (k+1) => if i=0 then S 0 else []) := by
     rw [hout]
     rfl
   have hr' : run (tm P).m (Turing.initList (tm P) input) m=some (Turing.haltList (tm P) output) := by
     rw [hstart,hfinish]
     exact hr
   obtain ⟨hout'⟩ := RawStack.outputs (tm := tm P) input output m hr'
   have hbound : m ≤ input.length+(k+2)*T+2*k+5 := hm.trans (by nlinarith)
   have hh : Nonempty (Turing.TM2OutputsInTime (tm P) input (some output) (input.length+(k+2)*T+2*k+5)) :=
     ⟨{ hout' with steps_le_m := hout'.steps_le_m.trans hbound }⟩
   change Nonempty (Turing.TM2OutputsInTime (tm P) (input.map id) (some (output.map id)) (input.length+(k+2)*T+2*k+5))
   dsimp only [tm] at hh ⊢
   simpa only [List.map_id] using hh
   

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.RoutineProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler

 theorem runs_mono (P : EdgeSublinearMWIS.Main.Program) (input output : List Bool) {t u : ℕ}
    (ht : EdgeSublinearMWIS.Main.Runs P input output t) (htu : t≤ u) :
    EdgeSublinearMWIS.Main.Runs P input output u := by
  obtain ⟨h⟩ := ht
  exact ⟨{h with steps_le_m := h.steps_le_m.trans htu}⟩

 def routineProgram {f : Data → Data} {charge : Data → ℕ} (R : Routine f charge) : EdgeSublinearMWIS.Main.Program :=
   program R.rawProgram.program

 def routineFactor {f : Data → Data} {charge : Data → ℕ} (R : Routine f charge) : ℕ :=
   2000*(Fintype.card R.Vars+7)

 theorem routine_runs {f : Data → Data} {charge : Data → ℕ} (R : Routine f charge)
    (input output : List Bool) (hf : f (enc input)=enc output) :
    EdgeSublinearMWIS.Main.Runs (routineProgram R) input output
      (routineFactor R*(charge (enc input)+input.length+output.length+1)) := by
  obtain ⟨S,hS,hout⟩ := R.rawProgram_runs input output hf
  have hr := program_runs R.rawProgram.program input output
    (1000*(charge (enc input)+input.length+output.length+1)) ⟨S,hS,hout⟩
  apply runs_mono _ _ _ hr
  let z := charge (enc input)+input.length+output.length+1
  have hz : 1≤ z := by dsimp [z]; omega
  have hL : input.length≤ z := by dsimp [z]; omega
  change input.length+(Fintype.card R.Vars+4+2)*(1000*z)+2*(Fintype.card R.Vars+4)+5 ≤ routineFactor R*z
  unfold routineFactor
  nlinarith

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.Sol_realizer_native
noncomputable section

open scoped Classical
set_option autoImplicit false
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main

theorem solution (f : List Bool → List Bool) (R : Realizer f) :
    ∃ (P : EdgeSublinearMWIS.Main.Program) (K : ℕ),0< K ∧ ∀input,
      Runs P input (f input) (K*(R.time input+input.length+(f input).length+1)) := by
  refine ⟨TreeToTM2.routineProgram R.routine,TreeToTM2.routineFactor R.routine,?_,?_⟩
  · unfold TreeToTM2.routineFactor
    positivity
  · intro input
    exact TreeToTM2.routine_runs R.routine input (f input) (R.correct input)
end
