-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_seq
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:11:52.682914+00:00
-- url     : https://prove2.me/submissions/2e445ba7-3930-4863-b119-0d4c79a459db

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

noncomputable section

open Classical
open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_Seq_Aux

open Turing Polynomial Function
open OAI.MetricKMedian.Binary

/-! ### Part 1: Finite-TM2 Composition, Fanout, and Output-Length Bounds -/

section TM2Plumbing

def tmPushes {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + tmPushes q
  | .peek _ _ q => tmPushes q
  | .pop _ _ q => tmPushes q
  | .load _ q => tmPushes q
  | .branch _ q r => max (tmPushes q) (tmPushes r)
  | .goto _ => 0
  | .halt => 0

def tmVolume {K : Type} [Fintype K] {Γ : K → Type} (s : ∀ k, List (Γ k)) : ℕ :=
  ∑ k : K, (s k).length

lemma tmVolume_update {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type}
    (s : ∀ k, List (Γ k)) (k : K) (v : List (Γ k)) :
    tmVolume (Function.update s k v) + (s k).length = tmVolume s + v.length := by
  unfold tmVolume
  have he : (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

lemma stepAux_tmVolume {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type}
    (q : TM2.Stmt Γ Λ σ) (v : σ) (s : ∀ k, List (Γ k)) :
    tmVolume (TM2.stepAux q v s).stk ≤ tmVolume s + tmPushes q := by
  induction q generalizing v s with
  | push k g q ih =>
    have h := ih v (Function.update s k (g v :: s k))
    have hv := tmVolume_update s k (g v :: s k)
    simp only [List.length_cons] at hv
    simpa only [TM2.stepAux, tmPushes, Nat.add_assoc] using
      (by omega : tmVolume (TM2.stepAux q v (Function.update s k (g v :: s k))).stk ≤
        tmVolume s + (1 + tmPushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
    have h := ih (g v (s k).head?) (Function.update s k (s k).tail)
    have hv := tmVolume_update s k (s k).tail
    have hl := List.length_tail (l := s k)
    simp only [TM2.stepAux, tmPushes]
    omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
    cases hg : g v
    · simpa only [TM2.stepAux, hg, Bool.false_eq_true, Bool.cond_false, tmPushes] using
        (ihr v s).trans (Nat.add_le_add_left (le_max_right (tmPushes q) _) _)
    · simpa only [TM2.stepAux, hg, Bool.cond_true, tmPushes] using
        (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (tmPushes r)) _)
  | goto g => simp only [TM2.stepAux, tmPushes, Nat.add_zero, le_rfl]
  | halt => simp only [TM2.stepAux, tmPushes, Nat.add_zero, le_rfl]

def tmGrowth (tm : FinTM2) : ℕ :=
  @Finset.univ tm.Λ tm.ΛFin |>.sum fun l => tmPushes (tm.m l)

lemma finTM2_step_volume (tm : FinTM2) (a b : tm.Cfg) (h : tm.step a = some b) :
    @tmVolume tm.K tm.kFin tm.Γ b.stk ≤ @tmVolume tm.K tm.kFin tm.Γ a.stk + tmGrowth tm := by
  let _ := tm.kDecidableEq
  let _ := tm.kFin
  let _ := tm.ΛFin
  rcases a with ⟨l, v, s⟩
  cases l with
  | none => cases h
  | some l =>
    have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
    rw [hb]
    exact (stepAux_tmVolume _ _ _).trans (Nat.add_le_add_left
      (Finset.single_le_sum (f := fun x => tmPushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)) _)

lemma finTM2_trace_volume (tm : FinTM2) {n : ℕ} {a b : tm.Cfg}
    (h : Trace tm.step n a b) :
    @tmVolume tm.K tm.kFin tm.Γ b.stk ≤
      @tmVolume tm.K tm.kFin tm.Γ a.stk + n * tmGrowth tm := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
    have hs := finTM2_step_volume tm a b hab
    calc
      _ ≤ @tmVolume tm.K tm.kFin tm.Γ b.stk + n * tmGrowth tm := ih
      _ ≤ @tmVolume tm.K tm.kFin tm.Γ a.stk + (n + 1) * tmGrowth tm := by rw [Nat.add_mul]; omega

lemma tmVolume_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) :
    @tmVolume tm.K tm.kFin tm.Γ (initList tm s).stk = s.length := by
  let _ := tm.kDecidableEq
  let _ := tm.kFin
  unfold tmVolume
  have he : (fun k => ((initList tm s).stk k).length) =
      fun k => if k = tm.k₀ then s.length else 0 := by
    funext k
    by_cases h : k = tm.k₀
    · subst h; simp [initList]
    · simp [initList, h]
  rw [he, Finset.sum_ite_eq']
  simp

lemma tmVolume_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) :
    @tmVolume tm.K tm.kFin tm.Γ (haltList tm s).stk = s.length := by
  let _ := tm.kDecidableEq
  let _ := tm.kFin
  unfold tmVolume
  have he : (fun k => ((haltList tm s).stk k).length) =
      fun k => if k = tm.k₁ then s.length else 0 := by
    funext k
    by_cases h : k = tm.k₁
    · subst h; simp [haltList]
    · simp [haltList, h]
  rw [he, Finset.sum_ite_eq']
  simp

lemma finTM2_output_length (tm : FinTM2) {s : List (tm.Γ tm.k₀)} {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) :
    t.length ≤ s.length + n * tmGrowth tm := by
  have ht : Trace tm.step h.steps (initList tm s) (haltList tm t) :=
    Trace.of_iterate h.evals_in_steps
  have hv := finTM2_trace_volume tm ht
  rw [tmVolume_initList, tmVolume_haltList] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

structure DepEmbedding (K L S : Type) {Γ : K → Type}
    (K' L' S' : Type) {Γ' : K' → Type} [DecidableEq K] [DecidableEq K'] where
  key : K → K'
  eΓ : ∀ k, Γ k ≃ Γ' (key k)
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v) = v
  write_state : ∀ v w, write (state v) w = state w
  stack : (∀ k, List (Γ k)) → (∀ k', List (Γ' k'))
  stack_key : ∀ s k, stack s (key k) = (s k).map (eΓ k)
  stack_update : ∀ s k x,
    stack (Function.update s k x) = Function.update (stack s) (key k) (x.map (eΓ k))
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt Γ' L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s) = ⟨halted, state v, stack s⟩

namespace DepEmbedding
variable {K L S : Type} {Γ : K → Type} {K' L' S' : Type} {Γ' : K' → Type}
variable [DecidableEq K] [DecidableEq K']
variable (E : DepEmbedding K L S K' L' S' (Γ := Γ) (Γ' := Γ'))

def stmt : TM2.Stmt Γ L S → TM2.Stmt Γ' L' S'
  | .push k f q => .push (E.key k) (fun v => E.eΓ k (f (E.read v))) (stmt q)
  | .peek k f q => .peek (E.key k) (fun v x => E.write v (f (E.read v) (x.map (E.eΓ k).symm))) (stmt q)
  | .pop k f q => .pop (E.key k) (fun v x => E.write v (f (E.read v) (x.map (E.eΓ k).symm))) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg Γ L S) : TM2.Cfg Γ' L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)), E.state a.var, E.stack a.stk⟩

lemma stepAux_stmt (q : TM2.Stmt Γ L S) (v : S) (s : ∀ k, List (Γ k)) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s) = E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
    simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, ← List.map_cons, ← E.stack_update]
    exact ih _ _
  | peek k f q ih =>
    simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, List.head?_map, Option.map_map,
      Function.comp_def, Equiv.symm_apply_apply, Option.map_id', E.write_state]
    exact ih _ _
  | pop k f q ih =>
    simp only [stmt, TM2.stepAux, E.read_state, E.stack_key, List.head?_map, Option.map_map,
      Function.comp_def, Equiv.symm_apply_apply, Option.map_id', E.write_state, ← List.map_tail,
      ← E.stack_update]
    exact ih _ _
  | load f q ih =>
    simp only [stmt, TM2.stepAux, E.read_state, E.write_state]
    exact ih _ _
  | branch f q r ihq ihr =>
    cases h : f v <;> simp only [stmt, TM2.stepAux, E.read_state, h, Bool.cond_false, Bool.cond_true]
    · exact ihr _ _
    · exact ihq _ _
  | goto f => simp only [stmt, TM2.stepAux, E.read_state, cfg, Option.elim_some]
  | halt => exact E.stop_spec v s

lemma step_cfg (m : L → TM2.Stmt Γ L S) (m' : L' → TM2.Stmt Γ' L' S')
    (hm : ∀ l, m' (E.label l) = E.stmt (m l))
    (a b : TM2.Cfg Γ L S) (h : TM2.step m a = some b) :
    TM2.step m' (E.cfg a) = some (E.cfg b) := by
  rcases a with ⟨l, v, s⟩
  cases l with
  | none => cases h
  | some l =>
    have hb : b = TM2.stepAux (m l) v s := (Option.some.inj h).symm
    subst b
    simp only [cfg, Option.elim_some, TM2.step, hm]
    exact congrArg some (E.stepAux_stmt (m l) v s)

lemma trace (m : L → TM2.Stmt Γ L S) (m' : L' → TM2.Stmt Γ' L' S')
    (hm : ∀ l, m' (E.label l) = E.stmt (m l))
    {n : ℕ} {a b : TM2.Cfg Γ L S} (h : Trace (TM2.step m) n a b) :
    Trace (TM2.step m') n (E.cfg a) (E.cfg b) :=
  h.map E.cfg (E.step_cfg m m' hm)

end DepEmbedding

lemma dep_cfg_ext {K : Type} {Γ : K → Type} {L S : Type} {a b : TM2.Cfg Γ L S}
    (hl : a.l = b.l) (hv : a.var = b.var) (hs : a.stk = b.stk) : a = b := by
  cases a; cases b; cases hl; cases hv; cases hs; rfl

lemma list_map_equiv_refl {α : Type*} (l : List α) : l.map (Equiv.refl α) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) ih

namespace TM2Comp
variable {f g : Str → Str}
variable (M : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f)
variable (N : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) g)

abbrev Key := M.tm.K ⊕ (Unit ⊕ N.tm.K)

@[reducible] def Γ : Key M N → Type
  | .inl k => M.tm.Γ k
  | .inr (.inl _) => Bool
  | .inr (.inr k) => N.tm.Γ k

local instance : DecidableEq M.tm.K := M.tm.kDecidableEq
local instance : Fintype M.tm.K := M.tm.kFin
local instance : Fintype M.tm.Λ := M.tm.ΛFin
local instance : Fintype M.tm.σ := M.tm.σFin
local instance : Fintype (M.tm.Γ M.tm.k₀) := M.tm.Γk₀Fin
local instance : DecidableEq N.tm.K := N.tm.kDecidableEq
local instance : Fintype N.tm.K := N.tm.kFin
local instance : Fintype N.tm.Λ := N.tm.ΛFin
local instance : Fintype N.tm.σ := N.tm.σFin
local instance : Fintype (N.tm.Γ N.tm.k₀) := N.tm.Γk₀Fin

abbrev Label := M.tm.Λ ⊕ (Bool ⊕ N.tm.Λ)
abbrev State := M.tm.σ × N.tm.σ × Option Bool

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxKey : Key M N := .inr (.inl ())
abbrev Cfg := TM2.Cfg (Γ M N) (Label M N) (State M N)

def leftStack (s : ∀ k, List (M.tm.Γ k)) : ∀ k', List (Γ M N k')
  | .inl k => s k
  | .inr _ => []

def left : DepEmbedding M.tm.K M.tm.Λ M.tm.σ (Key M N) (Label M N) (State M N)
    (Γ := M.tm.Γ) (Γ' := Γ M N) where
  key := Sum.inl
  eΓ _ := Equiv.refl _
  read := Prod.fst
  write v x := (x, v.2)
  state v := (v, N.tm.initialState, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack := leftStack M N
  stack_key s k := (list_map_equiv_refl (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | j
    · by_cases h : j = k
      · subst h
        dsimp [leftStack]
        rw [Function.update_self, Function.update_self]
        exact (list_map_equiv_refl x).symm
      · dsimp [leftStack]
        rw [Function.update_of_ne h, Function.update_of_ne (fun he => h (Sum.inl.inj he))]
        rfl
    · dsimp [leftStack]
      rw [Function.update_of_ne (by simp)]
      rfl
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def rightStack (s : ∀ k, List (N.tm.Γ k)) : ∀ k', List (Γ M N k')
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr k) => s k

def right : DepEmbedding N.tm.K N.tm.Λ N.tm.σ (Key M N) (Label M N) (State M N)
    (Γ := N.tm.Γ) (Γ' := Γ M N) where
  key k := .inr (.inr k)
  eΓ _ := Equiv.refl _
  read v := v.2.1
  write v x := (v.1, x, v.2.2)
  state v := (M.tm.initialState, v, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack := rightStack M N
  stack_key s k := (list_map_equiv_refl (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | j
    · dsimp [rightStack]
      rw [Function.update_of_ne (by simp)]
      rfl
    · rcases j with j | j
      · dsimp [rightStack]
        rw [Function.update_of_ne (by simp)]
        rfl
      · by_cases h : j = k
        · subst h
          dsimp [rightStack]
          rw [Function.update_self, Function.update_self]
          exact (list_map_equiv_refl x).symm
        · dsimp [rightStack]
          rw [Function.update_of_ne h, Function.update_of_ne (fun he => h (Sum.inr.inj (Sum.inr.inj he)))]
          rfl
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def clean (v : State M N) : State M N := (v.1, v.2.1, none)

def transfer : Bool → TM2.Stmt (Γ M N) (Label M N) (State M N)
  | false =>
    .pop (.inl M.tm.k₁) (fun v c => (v.1, v.2.1, c.map M.outputAlphabet))
      (.branch (fun v => v.2.2.isSome)
        (.push (auxKey M N) (fun v => v.2.2.getD false)
          (.load (clean M N) (.goto (fun _ => phaseLabel M N false))))
        (.load (clean M N) (.goto (fun _ => phaseLabel M N true))))
  | true =>
    .pop (auxKey M N) (fun v c => (v.1, v.2.1, c))
      (.branch (fun v => v.2.2.isSome)
        (.push (.inr (.inr N.tm.k₀)) (fun v => N.inputAlphabet.symm (v.2.2.getD false))
          (.load (clean M N) (.goto (fun _ => phaseLabel M N true))))
        (.load (clean M N) (.goto (fun _ => .inr (.inr N.tm.main)))))

def code : Label M N → TM2.Stmt (Γ M N) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.tm.m l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.tm.m l)

def tm : FinTM2 where
  K := Key M N
  kDecidableEq := inferInstance
  k₀ := .inl M.tm.k₀
  k₁ := .inr (.inr N.tm.k₁)
  Γ := Γ M N
  Λ := Label M N
  main := .inl M.tm.main
  σ := State M N
  initialState := (M.tm.initialState, N.tm.initialState, none)
  Γk₀Fin := M.tm.Γk₀Fin
  m := code M N

lemma step_eq (l : Label M N) (v : State M N) (s : ∀ k, List (Γ M N k)) :
    (tm M N).step (⟨some l, v, s⟩ : Cfg M N) =
      some (@TM2.stepAux (Key M N) (Γ M N) (Label M N) (State M N) inferInstance (code M N l) v s) :=
  rfl

def drainStk (xs : List (M.tm.Γ M.tm.k₁)) (ys : List Bool) (k : Key M N) : List (Γ M N k) :=
  match k with
  | .inl k => @dite (List (M.tm.Γ k)) (k = M.tm.k₁) (M.tm.kDecidableEq k M.tm.k₁)
      (fun h => by rw [h]; exact xs) (fun _ => [])
  | .inr (.inl _) => ys
  | .inr (.inr _) => []

def loadStk (xs : List Bool) (ys : List (N.tm.Γ N.tm.k₀)) (k : Key M N) : List (Γ M N k) :=
  match k with
  | .inl _ => []
  | .inr (.inl _) => xs
  | .inr (.inr k) => @dite (List (N.tm.Γ k)) (k = N.tm.k₀) (N.tm.kDecidableEq k N.tm.k₀)
      (fun h => by rw [h]; exact ys) (fun _ => [])

lemma initial_left (s : List Bool) :
    (left M N).cfg (initList M.tm (s.map M.inputAlphabet.symm)) =
      initList (tm M N) (s.map M.inputAlphabet.symm) := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · by_cases h : k = M.tm.k₀
    · subst h; simp [DepEmbedding.cfg, left, leftStack, initList, tm]; rfl
    · simp [DepEmbedding.cfg, left, leftStack, initList, tm, h]
  · rcases k with k | k <;> rfl

lemma final_right (s : List Bool) :
    (right M N).cfg (haltList N.tm (s.map N.outputAlphabet.symm)) =
      haltList (tm M N) (s.map N.outputAlphabet.symm) := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rfl
    · by_cases h : k = N.tm.k₁
      · subst h; simp [DepEmbedding.cfg, right, rightStack, haltList, tm]; rfl
      · simp [DepEmbedding.cfg, right, rightStack, haltList, tm, h]

lemma left_halt_drain (xs : List (M.tm.Γ M.tm.k₁)) :
    (left M N).cfg (haltList M.tm xs) =
      (⟨some (phaseLabel M N false), (M.tm.initialState, N.tm.initialState, none),
        drainStk M N xs []⟩ : Cfg M N) := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · by_cases h : k = M.tm.k₁
    · subst h; simp [DepEmbedding.cfg, left, leftStack, haltList, drainStk]
    · simp [DepEmbedding.cfg, left, leftStack, haltList, drainStk, h]
  · rcases k with k | k <;> rfl

lemma drain_cons (b : M.tm.Γ M.tm.k₁) (xs : List (M.tm.Γ M.tm.k₁)) (ys : List Bool) :
    (tm M N).step (⟨some (phaseLabel M N false), (M.tm.initialState, N.tm.initialState, none),
        drainStk M N (b :: xs) ys⟩ : Cfg M N) =
      some (⟨some (phaseLabel M N false), (M.tm.initialState, N.tm.initialState, none),
        drainStk M N xs (M.outputAlphabet b :: ys)⟩ : Cfg M N) := by
  rw [step_eq]
  apply congrArg some
  dsimp [code, transfer, TM2.stepAux]
  have h1 : drainStk M N (b :: xs) ys (.inl M.tm.k₁) = b :: xs := by simp [drainStk]
  rw [h1]
  dsimp [List.head?, List.tail, Option.map, Option.isSome, Option.getD, clean]
  apply dep_cfg_ext <;> try rfl
  funext k
  dsimp only
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [auxKey])]
    by_cases hk : k = M.tm.k₁
    · subst hk; rw [Function.update_self]; simp [drainStk]
    · rw [Function.update_of_ne (fun he => hk (Sum.inl.inj he))]; simp [drainStk, hk]
  · rcases k with k | k
    · rcases k with ⟨⟩; rw [Function.update_self, Function.update_of_ne (by simp [auxKey])]; rfl
    · rw [Function.update_of_ne (by simp [auxKey]), Function.update_of_ne (by simp)]; rfl

lemma drain_run (xs : List (M.tm.Γ M.tm.k₁)) (ys : List Bool) :
    Trace (tm M N).step xs.length
      (⟨some (phaseLabel M N false), (M.tm.initialState, N.tm.initialState, none),
        drainStk M N xs ys⟩ : Cfg M N)
      (⟨some (phaseLabel M N false), (M.tm.initialState, N.tm.initialState, none),
        drainStk M N [] ((xs.map M.outputAlphabet).reverse ++ ys)⟩ : Cfg M N) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons b xs ih =>
    have h := Trace.cons (drain_cons M N b xs ys) (ih (M.outputAlphabet b :: ys))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using h

lemma drain_nil (ys : List Bool) :
    (tm M N).step (⟨some (phaseLabel M N false), (M.tm.initialState, N.tm.initialState, none),
        drainStk M N [] ys⟩ : Cfg M N) =
      some (⟨some (phaseLabel M N true), (M.tm.initialState, N.tm.initialState, none),
        loadStk M N ys []⟩ : Cfg M N) := by
  rw [step_eq]
  apply congrArg some
  dsimp [code, transfer, TM2.stepAux]
  have h1 : drainStk M N [] ys (.inl M.tm.k₁) = [] := by simp [drainStk]
  rw [h1]
  dsimp [List.head?, List.tail, Option.map, Option.isSome, Option.getD, clean]
  apply dep_cfg_ext <;> try rfl
  funext k
  dsimp only
  rcases k with k | k
  · by_cases hk : k = M.tm.k₁
    · subst hk; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne (fun he => hk (Sum.inl.inj he))]; simp [drainStk, loadStk, hk]
  · rcases k with k | k
    · rw [Function.update_of_ne (by simp)]; rfl
    · rw [Function.update_of_ne (by simp)]
      by_cases hk : k = N.tm.k₀
      · subst hk; simp [drainStk, loadStk]
      · simp [drainStk, loadStk, hk]

lemma load_cons (b : Bool) (xs : List Bool) (ys : List (N.tm.Γ N.tm.k₀)) :
    (tm M N).step (⟨some (phaseLabel M N true), (M.tm.initialState, N.tm.initialState, none),
        loadStk M N (b :: xs) ys⟩ : Cfg M N) =
      some (⟨some (phaseLabel M N true), (M.tm.initialState, N.tm.initialState, none),
        loadStk M N xs (N.inputAlphabet.symm b :: ys)⟩ : Cfg M N) := by
  rw [step_eq]
  apply congrArg some
  dsimp [code, transfer, TM2.stepAux]
  have h1 : loadStk M N (b :: xs) ys (auxKey M N) = b :: xs := rfl
  rw [h1]
  dsimp [List.head?, List.tail, Option.isSome, Option.getD, clean]
  apply dep_cfg_ext <;> try rfl
  funext k
  dsimp only
  rcases k with k | k
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp [auxKey])]; rfl
  · rcases k with k | k
    · rcases k with ⟨⟩; rw [Function.update_of_ne (by simp), Function.update_self]; rfl
    · by_cases hk : k = N.tm.k₀
      · subst hk; rw [Function.update_self]; simp [loadStk]
      · rw [Function.update_of_ne (fun he => hk (Sum.inr.inj (Sum.inr.inj he))),
            Function.update_of_ne (by simp [auxKey])]
        simp [loadStk, hk]

lemma load_run (xs : List Bool) (ys : List (N.tm.Γ N.tm.k₀)) :
    Trace (tm M N).step xs.length
      (⟨some (phaseLabel M N true), (M.tm.initialState, N.tm.initialState, none),
        loadStk M N xs ys⟩ : Cfg M N)
      (⟨some (phaseLabel M N true), (M.tm.initialState, N.tm.initialState, none),
        loadStk M N [] (xs.reverse.map N.inputAlphabet.symm ++ ys)⟩ : Cfg M N) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons b xs ih =>
    have h := Trace.cons (load_cons M N b xs ys) (ih (N.inputAlphabet.symm b :: ys))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append] using h

lemma load_nil (ys : List (N.tm.Γ N.tm.k₀)) :
    (tm M N).step (⟨some (phaseLabel M N true), (M.tm.initialState, N.tm.initialState, none),
        loadStk M N [] ys⟩ : Cfg M N) =
      some ((right M N).cfg (initList N.tm ys)) := by
  rw [step_eq]
  apply congrArg some
  dsimp [code, transfer, TM2.stepAux]
  have h1 : loadStk M N [] ys (auxKey M N) = [] := rfl
  rw [h1]
  dsimp [List.head?, List.tail, Option.isSome, Option.getD, clean]
  apply dep_cfg_ext <;> try rfl
  funext k
  dsimp only [DepEmbedding.cfg, right, rightStack, initList]
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [auxKey])]; rfl
  · rcases k with k | k
    · rcases k with ⟨⟩; rw [Function.update_self]
    · rw [Function.update_of_ne (by simp [auxKey])]
      by_cases hk : k = N.tm.k₀
      · subst hk; simp [loadStk]
      · simp [loadStk, hk]

noncomputable def comp :
    TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) (g ∘ f) where
  tm := tm M N
  inputAlphabet := M.inputAlphabet
  outputAlphabet := N.outputAlphabet
  time :=
    let sizeBound := X + M.time * C (tmGrowth M.tm)
    M.time + 2 * sizeBound + 2 + N.time.comp sizeBound
  outputsFun s := by
    let hM := M.outputsFun s
    let hN := N.outputsFun (f s)
    have tM : Trace M.tm.step hM.steps (initList M.tm (s.map M.inputAlphabet.symm))
        (haltList M.tm ((f s).map M.outputAlphabet.symm)) := Trace.of_iterate hM.evals_in_steps
    have tN : Trace N.tm.step hN.steps (initList N.tm ((f s).map N.inputAlphabet.symm))
        (haltList N.tm ((g (f s)).map N.outputAlphabet.symm)) := Trace.of_iterate hN.evals_in_steps
    have h1 := (left M N).trace M.tm.m (tm M N).m (fun _ => rfl) tM
    rw [initial_left, left_halt_drain] at h1
    have hd := drain_run M N ((f s).map M.outputAlphabet.symm) []
    simp only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id',
      List.append_nil, List.length_map] at hd
    have hc := Trace.cons (drain_nil M N (f s).reverse) (Trace.refl _)
    have hl := load_run M N (f s).reverse []
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hl
    have he := Trace.cons (load_nil M N ((f s).map N.inputAlphabet.symm)) (Trace.refl _)
    have h2 := (right M N).trace N.tm.m (tm M N).m (fun _ => rfl) tN
    rw [final_right] at h2
    have hfull := ((((h1.trans hd).trans hc).trans hl).trans he).trans h2
    refine ⟨⟨_, hfull.iterate_eq⟩, ?_⟩
    have hlen : ((f s).map M.outputAlphabet.symm).length ≤
        (s.map M.inputAlphabet.symm).length + (M.time.eval s.length) * tmGrowth M.tm :=
      finTM2_output_length M.tm hM
    simp only [List.length_map] at hlen
    have hn : hN.steps ≤ N.time.eval (s.length + (M.time.eval s.length) * tmGrowth M.tm) :=
      hN.steps_le_m.trans (polynomial_eval_mono N.time hlen)
    have hm := hM.steps_le_m
    simp only [id_eq] at hm
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_comp, id_eq]
    omega

end TM2Comp

namespace TM2Fanout
variable {f1 f2 : Str → Str}
variable (M : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f1)
variable (N : TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f2)

abbrev Key := M.tm.K ⊕ (N.tm.K ⊕ Fin 3)

@[reducible] def Γ : Key M N → Type
  | .inl k => M.tm.Γ k
  | .inr (.inl k) => N.tm.Γ k
  | .inr (.inr _) => Bool

local instance : DecidableEq M.tm.K := M.tm.kDecidableEq
local instance : Fintype M.tm.K := M.tm.kFin
local instance : Fintype M.tm.Λ := M.tm.ΛFin
local instance : Fintype M.tm.σ := M.tm.σFin
local instance : Fintype (M.tm.Γ M.tm.k₀) := M.tm.Γk₀Fin
local instance : DecidableEq N.tm.K := N.tm.kDecidableEq
local instance : Fintype N.tm.K := N.tm.kFin
local instance : Fintype N.tm.Λ := N.tm.ΛFin
local instance : Fintype N.tm.σ := N.tm.σFin
local instance : Fintype (N.tm.Γ N.tm.k₀) := N.tm.Γk₀Fin

abbrev Label := M.tm.Λ ⊕ (N.tm.Λ ⊕ Fin 6)
abbrev State := M.tm.σ × N.tm.σ × Option Bool

abbrev inpKey : Key M N := .inr (.inr 0)
abbrev bufKey : Key M N := .inr (.inr 1)
abbrev outKey : Key M N := .inr (.inr 2)

abbrev phLabel (i : Fin 6) : Label M N := .inr (.inr i)
def clean (v : State M N) : State M N := (v.1, v.2.1, none)
abbrev Cfg := TM2.Cfg (Γ M N) (Label M N) (State M N)

def leftStack (nStk : ∀ k, List (N.tm.Γ k)) (s : ∀ k, List (M.tm.Γ k)) : ∀ k', List (Γ M N k')
  | .inl k => s k
  | .inr (.inl k) => nStk k
  | .inr (.inr _) => []

def left (nStk : ∀ k, List (N.tm.Γ k)) :
    DepEmbedding M.tm.K M.tm.Λ M.tm.σ (Key M N) (Label M N) (State M N)
      (Γ := M.tm.Γ) (Γ' := Γ M N) where
  key := Sum.inl
  eΓ _ := Equiv.refl _
  read := Prod.fst
  write v x := (x, v.2)
  state v := (v, N.tm.initialState, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack := leftStack M N nStk
  stack_key s k := (list_map_equiv_refl (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | j
    · by_cases h : j = k
      · subst h
        dsimp [leftStack]
        rw [Function.update_self, Function.update_self]
        exact (list_map_equiv_refl x).symm
      · dsimp [leftStack]
        rw [Function.update_of_ne h, Function.update_of_ne (fun he => h (Sum.inl.inj he))]
        rfl
    · rcases j with j | j <;> dsimp [leftStack] <;> rw [Function.update_of_ne (by simp)] <;> rfl
  label := Sum.inl
  halted := some (.inr (.inl N.tm.main))
  stop := .goto (fun _ => .inr (.inl N.tm.main))
  stop_spec _ _ := rfl

def rightStack (mStk : ∀ k, List (M.tm.Γ k)) (s : ∀ k, List (N.tm.Γ k)) : ∀ k', List (Γ M N k')
  | .inl k => mStk k
  | .inr (.inl k) => s k
  | .inr (.inr _) => []

def right (mStk : ∀ k, List (M.tm.Γ k)) :
    DepEmbedding N.tm.K N.tm.Λ N.tm.σ (Key M N) (Label M N) (State M N)
      (Γ := N.tm.Γ) (Γ' := Γ M N) where
  key k := .inr (.inl k)
  eΓ _ := Equiv.refl _
  read v := v.2.1
  write v x := (v.1, x, v.2.2)
  state v := (M.tm.initialState, v, none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack := rightStack M N mStk
  stack_key s k := (list_map_equiv_refl (s k)).symm
  stack_update s k x := by
    funext j
    rcases j with j | j
    · dsimp [rightStack]
      rw [Function.update_of_ne (by simp)]
      rfl
    · rcases j with j | j
      · by_cases h : j = k
        · subst h
          dsimp [rightStack]
          rw [Function.update_self, Function.update_self]
          exact (list_map_equiv_refl x).symm
        · dsimp [rightStack]
          rw [Function.update_of_ne h, Function.update_of_ne (fun he => h (Sum.inl.inj (Sum.inr.inj he)))]
          rfl
      · dsimp [rightStack]
        rw [Function.update_of_ne (by simp)]
        rfl
  label l := .inr (.inl l)
  halted := some (phLabel M N 2)
  stop := .goto (fun _ => phLabel M N 2)
  stop_spec _ _ := rfl

lemma left_stmt_indep (n1 n2 : ∀ k, List (N.tm.Γ k)) (q : TM2.Stmt M.tm.Γ M.tm.Λ M.tm.σ) :
    (left M N n1).stmt q = (left M N n2).stmt q := by
  induction q <;> simp_all [DepEmbedding.stmt, left] <;> rfl

lemma right_stmt_indep (m1 m2 : ∀ k, List (M.tm.Γ k)) (q : TM2.Stmt N.tm.Γ N.tm.Λ N.tm.σ) :
    (right M N m1).stmt q = (right M N m2).stmt q := by
  induction q <;> simp_all [DepEmbedding.stmt, right] <;> rfl

def phaseStmt : Fin 6 → TM2.Stmt (Γ M N) (Label M N) (State M N)
  | 0 =>
    .pop (inpKey M N) (fun v c => (v.1, v.2.1, c))
      (.branch (fun v => v.2.2.isSome)
        (.push (bufKey M N) (fun v => v.2.2.getD false)
          (.load (clean M N) (.goto (fun _ => phLabel M N 0))))
        (.load (clean M N) (.goto (fun _ => phLabel M N 1))))
  | 1 =>
    .pop (bufKey M N) (fun v c => (v.1, v.2.1, c))
      (.branch (fun v => v.2.2.isSome)
        (.push (.inl M.tm.k₀) (fun v => M.inputAlphabet.symm (v.2.2.getD false))
          (.push (.inr (.inl N.tm.k₀)) (fun v => N.inputAlphabet.symm (v.2.2.getD false))
            (.load (clean M N) (.goto (fun _ => phLabel M N 1)))))
        (.load (clean M N) (.goto (fun _ => .inl M.tm.main))))
  | 2 =>
    .pop (.inr (.inl N.tm.k₁)) (fun v c => (v.1, v.2.1, c.map N.outputAlphabet))
      (.branch (fun v => v.2.2.isSome)
        (.push (bufKey M N) (fun v => v.2.2.getD false)
          (.load (clean M N) (.goto (fun _ => phLabel M N 2))))
        (.load (clean M N) (.goto (fun _ => phLabel M N 3))))
  | 3 =>
    .pop (bufKey M N) (fun v c => (v.1, v.2.1, c))
      (.branch (fun v => v.2.2.isSome)
        (.push (outKey M N) (fun v => v.2.2.getD false)
          (.load (clean M N) (.goto (fun _ => phLabel M N 3))))
        (.push (outKey M N) (fun _ => false)
          (.load (clean M N) (.goto (fun _ => phLabel M N 4)))))
  | 4 =>
    .pop (.inl M.tm.k₁) (fun v c => (v.1, v.2.1, c.map M.outputAlphabet))
      (.branch (fun v => v.2.2.isSome)
        (.push (bufKey M N) (fun v => v.2.2.getD false)
          (.load (clean M N) (.goto (fun _ => phLabel M N 4))))
        (.load (clean M N) (.goto (fun _ => phLabel M N 5))))
  | 5 =>
    .pop (bufKey M N) (fun v c => (v.1, v.2.1, c))
      (.branch (fun v => v.2.2.isSome)
        (.push (outKey M N) (fun v => v.2.2.getD false)
          (.push (outKey M N) (fun _ => true)
            (.load (clean M N) (.goto (fun _ => phLabel M N 5)))))
        (.load (clean M N) .halt))

def code : Label M N → TM2.Stmt (Γ M N) (Label M N) (State M N)
  | .inl l => (left M N (fun _ => [])).stmt (M.tm.m l)
  | .inr (.inl l) => (right M N (fun _ => [])).stmt (N.tm.m l)
  | .inr (.inr i) => phaseStmt M N i

def tm : FinTM2 where
  K := Key M N
  kDecidableEq := inferInstance
  k₀ := inpKey M N
  k₁ := outKey M N
  Γ := Γ M N
  Λ := Label M N
  main := phLabel M N 0
  σ := State M N
  initialState := (M.tm.initialState, N.tm.initialState, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := code M N

lemma step_eq (l : Label M N) (v : State M N) (s : ∀ k, List (Γ M N k)) :
    (tm M N).step (⟨some l, v, s⟩ : Cfg M N) =
      some (@TM2.stepAux (Key M N) (Γ M N) (Label M N) (State M N) inferInstance (code M N l) v s) :=
  rfl

def stk (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) : ∀ k, List (Γ M N k)
  | .inl k => ms k
  | .inr (.inl k) => ns k
  | .inr (.inr 0) => is
  | .inr (.inr 1) => bs
  | .inr (.inr 2) => os

lemma stk_update_inp (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os is' : List Bool) :
    Function.update (stk M N ms ns is bs os) (inpKey M N) is' = stk M N ms ns is' bs os := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [inpKey])]; rfl
  · rcases k with k | k
    · rw [Function.update_of_ne (by simp [inpKey])]; rfl
    · fin_cases k
      · change Function.update (stk M N ms ns is bs os) (inpKey M N) is' (inpKey M N) = _
        rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (by
          intro h; exact absurd (Fin.val_eq_of_eq (Sum.inr.inj (Sum.inr.inj h))) (by decide))]; rfl
      · rw [Function.update_of_ne (by
          intro h; exact absurd (Fin.val_eq_of_eq (Sum.inr.inj (Sum.inr.inj h))) (by decide))]; rfl

lemma stk_update_buf (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os bs' : List Bool) :
    Function.update (stk M N ms ns is bs os) (bufKey M N) bs' = stk M N ms ns is bs' os := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [bufKey])]; rfl
  · rcases k with k | k
    · rw [Function.update_of_ne (by simp [bufKey])]; rfl
    · fin_cases k
      · rw [Function.update_of_ne (by
          intro h; exact absurd (Fin.val_eq_of_eq (Sum.inr.inj (Sum.inr.inj h))) (by decide))]; rfl
      · change Function.update (stk M N ms ns is bs os) (bufKey M N) bs' (bufKey M N) = _
        rw [Function.update_self]; rfl
      · rw [Function.update_of_ne (by
          intro h; exact absurd (Fin.val_eq_of_eq (Sum.inr.inj (Sum.inr.inj h))) (by decide))]; rfl

lemma stk_update_out (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os os' : List Bool) :
    Function.update (stk M N ms ns is bs os) (outKey M N) os' = stk M N ms ns is bs os' := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [outKey])]; rfl
  · rcases k with k | k
    · rw [Function.update_of_ne (by simp [outKey])]; rfl
    · fin_cases k
      · rw [Function.update_of_ne (by
          intro h; exact absurd (Fin.val_eq_of_eq (Sum.inr.inj (Sum.inr.inj h))) (by decide))]; rfl
      · rw [Function.update_of_ne (by
          intro h; exact absurd (Fin.val_eq_of_eq (Sum.inr.inj (Sum.inr.inj h))) (by decide))]; rfl
      · change Function.update (stk M N ms ns is bs os) (outKey M N) os' (outKey M N) = _
        rw [Function.update_self]; rfl

lemma stk_update_left (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) (k : M.tm.K) (v : List (M.tm.Γ k)) :
    Function.update (stk M N ms ns is bs os) (.inl k) v =
      stk M N (Function.update ms k v) ns is bs os := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h; dsimp [stk]; rw [Function.update_self, Function.update_self]
    · dsimp [stk]; rw [Function.update_of_ne (fun he => h (Sum.inl.inj he)), Function.update_of_ne h]
      rfl
  · rw [Function.update_of_ne (by simp)]
    rcases j with j | j
    · rfl
    · fin_cases j <;> rfl

lemma stk_update_right (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) (k : N.tm.K) (v : List (N.tm.Γ k)) :
    Function.update (stk M N ms ns is bs os) (.inr (.inl k)) v =
      stk M N ms (Function.update ns k v) is bs os := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rcases j with j | j
    · by_cases h : j = k
      · subst h; dsimp [stk]; rw [Function.update_self, Function.update_self]
      · dsimp [stk]; rw [Function.update_of_ne (fun he => h (Sum.inl.inj (Sum.inr.inj he))), Function.update_of_ne h]
        rfl
    · rw [Function.update_of_ne (by simp)]
      fin_cases j <;> rfl

def phCfg (i : Fin 6) (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) : Cfg M N :=
  ⟨some (phLabel M N i), (M.tm.initialState, N.tm.initialState, none), stk M N ms ns is bs os⟩

lemma init_eq_ph0 (s : List Bool) :
    (initList (tm M N) s : Cfg M N) = phCfg M N 0 (fun _ => []) (fun _ => []) s [] [] := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rfl
    · fin_cases k <;> rfl

lemma halt_eq (s : List Bool) :
    (haltList (tm M N) s : Cfg M N) = ⟨none, (M.tm.initialState, N.tm.initialState, none),
      stk M N (fun _ => []) (fun _ => []) [] [] s⟩ := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rfl
    · fin_cases k <;> rfl

lemma copy_run (is bs : List Bool) :
    Trace (tm M N).step (is.length + 1)
      (phCfg M N 0 (fun _ => []) (fun _ => []) is bs [])
      (phCfg M N 1 (fun _ => []) (fun _ => []) [] (is.reverse ++ bs) []) := by
  induction is generalizing bs with
  | nil =>
    refine Trace.cons ?_ (Trace.refl _)
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome, clean]
    rw [stk_update_inp]
  | cons b is ih =>
    refine Trace.cons ?_ (by
      have ih' := ih (b :: bs)
      dsimp only [FinTM2.Cfg] at ih' ⊢
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih')
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome,
      Option.getD, clean]
    rw [stk_update_inp, stk_update_buf]; rfl

lemma dist_cons (b : Bool) (bs : List Bool) (ms : ∀ k, List (M.tm.Γ k))
    (ns : ∀ k, List (N.tm.Γ k)) :
    (tm M N).step (phCfg M N 1 ms ns [] (b :: bs) []) =
      some (phCfg M N 1
        (Function.update ms M.tm.k₀ (M.inputAlphabet.symm b :: ms M.tm.k₀))
        (Function.update ns N.tm.k₀ (N.inputAlphabet.symm b :: ns N.tm.k₀)) [] bs []) := by
  dsimp only [phCfg]; rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome,
    Option.getD, clean]
  rw [stk_update_buf, stk_update_left, stk_update_right]
  dsimp [stk]

lemma dist_run (bs : List Bool) (ms : List (M.tm.Γ M.tm.k₀)) (ns : List (N.tm.Γ N.tm.k₀)) :
    Trace (tm M N).step (bs.length + 1)
      (phCfg M N 1
        (Function.update (fun _ => []) M.tm.k₀ ms)
        (Function.update (fun _ => []) N.tm.k₀ ns) [] bs [])
      ((left M N (Function.update (fun _ => []) N.tm.k₀
          (bs.reverse.map N.inputAlphabet.symm ++ ns))).cfg
        (initList M.tm (bs.reverse.map M.inputAlphabet.symm ++ ms))) := by
  induction bs generalizing ms ns with
  | nil =>
    refine Trace.cons ?_ (Trace.refl _)
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome, clean]
    rw [stk_update_buf]
    apply dep_cfg_ext <;> try rfl
    funext k
    rcases k with k | k
    · by_cases h : k = M.tm.k₀
      · subst h; simp [DepEmbedding.cfg, left, leftStack, initList, stk, Function.update]
      · simp [DepEmbedding.cfg, left, leftStack, initList, stk, Function.update, h]
    · rcases k with k | k
      · by_cases h : k = N.tm.k₀
        · subst h; simp [DepEmbedding.cfg, left, leftStack, initList, stk, Function.update]
        · simp [DepEmbedding.cfg, left, leftStack, initList, stk, Function.update, h]
      · fin_cases k <;> rfl
  | cons b bs ih =>
    have hstep := dist_cons M N b bs (Function.update (fun _ => []) M.tm.k₀ ms)
      (Function.update (fun _ => []) N.tm.k₀ ns)
    simp only [Function.update_idem, Function.update_self] at hstep
    refine Trace.cons hstep ?_
    have ih' := ih (M.inputAlphabet.symm b :: ms) (N.inputAlphabet.symm b :: ns)
    dsimp only [FinTM2.Cfg] at ih' ⊢
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append] using ih'

lemma left_halt_eq_right_init (s : List Bool) :
    (left M N (Function.update (fun _ => []) N.tm.k₀ (s.map N.inputAlphabet.symm))).cfg
        (haltList M.tm ((f1 s).map M.outputAlphabet.symm)) =
      (right M N (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))).cfg
        (initList N.tm (s.map N.inputAlphabet.symm)) := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · by_cases h : k = M.tm.k₁
    · subst h; simp [DepEmbedding.cfg, left, leftStack, right, rightStack, haltList, initList, Function.update]
    · simp [DepEmbedding.cfg, left, leftStack, right, rightStack, haltList, initList, Function.update, h]
  · rcases k with k | k
    · by_cases h : k = N.tm.k₀
      · subst h; simp [DepEmbedding.cfg, left, leftStack, right, rightStack, haltList, initList, Function.update]
      · simp [DepEmbedding.cfg, left, leftStack, right, rightStack, haltList, initList, Function.update, h]
    · rfl

lemma right_halt_eq_ph2 (s : List Bool) :
    (right M N (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))).cfg
        (haltList N.tm ((f2 s).map N.outputAlphabet.symm)) =
      phCfg M N 2
        (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))
        (Function.update (fun _ => []) N.tm.k₁ ((f2 s).map N.outputAlphabet.symm)) [] [] [] := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · by_cases h : k = N.tm.k₁
      · subst h; simp [DepEmbedding.cfg, right, rightStack, haltList, phCfg, stk, Function.update]
      · simp [DepEmbedding.cfg, right, rightStack, haltList, phCfg, stk, Function.update, h]
    · fin_cases k <;> rfl

lemma drain2_run (ms : ∀ k, List (M.tm.Γ k)) (ns : List (N.tm.Γ N.tm.k₁)) (bs : List Bool) :
    Trace (tm M N).step (ns.length + 1)
      (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ ns) [] bs [])
      (phCfg M N 3 ms (fun _ => []) [] ((ns.map N.outputAlphabet).reverse ++ bs) []) := by
  induction ns generalizing bs with
  | nil =>
    refine Trace.cons ?_ (Trace.refl _)
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk]
    rw [Function.update_self]
    dsimp [List.head?, List.tail, Option.map, Option.isSome, clean]
    rw [stk_update_right, Function.update_idem]
    apply dep_cfg_ext <;> try rfl
    funext k
    rcases k with k | k
    · rfl
    · rcases k with k | k
      · by_cases h : k = N.tm.k₁
        · subst h; simp [stk, Function.update]
        · simp [stk, Function.update, h]
      · fin_cases k <;> rfl
  | cons b ns ih =>
    have hstep : (tm M N).step (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ (b :: ns))
        [] bs []) =
      some (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ ns)
        [] (N.outputAlphabet b :: bs) []) := by
      dsimp only [phCfg]; rw [step_eq]
      apply congrArg some
      dsimp [code, phaseStmt, TM2.stepAux, stk]
      rw [Function.update_self]
      dsimp [List.head?, List.tail, Option.map, Option.isSome, Option.getD, clean]
      rw [stk_update_right, stk_update_buf, Function.update_idem]
      rfl
    refine Trace.cons hstep ?_
    have ih' := ih (N.outputAlphabet b :: bs)
    dsimp only [FinTM2.Cfg] at ih' ⊢
    simpa only [List.length_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using ih'

lemma emit2_run (ms : ∀ k, List (M.tm.Γ k)) (bs os : List Bool) :
    Trace (tm M N).step (bs.length + 1)
      (phCfg M N 3 ms (fun _ => []) [] bs os)
      (phCfg M N 4 ms (fun _ => []) [] [] (false :: (bs.reverse ++ os))) := by
  induction bs generalizing os with
  | nil =>
    refine Trace.cons ?_ (Trace.refl _)
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome, clean]
    rw [stk_update_buf, stk_update_out]; rfl
  | cons b bs ih =>
    refine Trace.cons ?_ (by
      have ih' := ih (b :: os)
      dsimp only [FinTM2.Cfg] at ih' ⊢
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih')
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome,
      Option.getD, clean]
    rw [stk_update_buf, stk_update_out]; rfl

lemma drain1_run (ms : List (M.tm.Γ M.tm.k₁)) (bs os : List Bool) :
    Trace (tm M N).step (ms.length + 1)
      (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ ms) (fun _ => []) [] bs os)
      (phCfg M N 5 (fun _ => []) (fun _ => []) [] ((ms.map M.outputAlphabet).reverse ++ bs) os) := by
  induction ms generalizing bs with
  | nil =>
    refine Trace.cons ?_ (Trace.refl _)
    dsimp only [phCfg]; rw [step_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk]
    rw [Function.update_self]
    dsimp [List.head?, List.tail, Option.map, Option.isSome, clean]
    rw [stk_update_left, Function.update_idem]
    apply dep_cfg_ext <;> try rfl
    funext k
    rcases k with k | k
    · by_cases h : k = M.tm.k₁
      · subst h; simp [stk, Function.update]
      · simp [stk, Function.update, h]
    · rcases k with k | k
      · rfl
      · fin_cases k <;> rfl
  | cons b ms ih =>
    have hstep : (tm M N).step (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ (b :: ms))
        (fun _ => []) [] bs os) =
      some (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ ms)
        (fun _ => []) [] (M.outputAlphabet b :: bs) os) := by
      dsimp only [phCfg]; rw [step_eq]
      apply congrArg some
      dsimp [code, phaseStmt, TM2.stepAux, stk]
      rw [Function.update_self]
      dsimp [List.head?, List.tail, Option.map, Option.isSome, Option.getD, clean]
      rw [stk_update_left, stk_update_buf, Function.update_idem]
      rfl
    refine Trace.cons hstep ?_
    have ih' := ih (M.outputAlphabet b :: bs)
    dsimp only [FinTM2.Cfg] at ih' ⊢
    simpa only [List.length_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using ih'

lemma emit1_run (bs os : List Bool) :
    Trace (tm M N).step (bs.length + 1)
      (phCfg M N 5 (fun _ => []) (fun _ => []) [] bs os)
      (haltList (tm M N) ((bs.reverse.flatMap fun b => [true, b]) ++ os)) := by
  induction bs generalizing os with
  | nil =>
    refine Trace.cons ?_ (Trace.refl _)
    dsimp only [phCfg]; rw [step_eq, halt_eq]
    apply congrArg some
    dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome, clean]
    rw [stk_update_buf]; rfl
  | cons b bs ih =>
    have hstep : (tm M N).step (phCfg M N 5 (fun _ => []) (fun _ => []) [] (b :: bs) os) =
        some (phCfg M N 5 (fun _ => []) (fun _ => []) [] bs (true :: b :: os)) := by
      dsimp only [phCfg]; rw [step_eq]
      apply congrArg some
      dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, List.tail, Option.isSome,
        Option.getD, clean]
      rw [stk_update_buf, stk_update_out, stk_update_out]; rfl
    refine Trace.cons hstep ?_
    have ih' := ih (true :: b :: os)
    dsimp only [FinTM2.Cfg] at ih' ⊢
    simpa only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
      using ih'

lemma quote_eq_flatMap (xs ys : List Bool) :
    (xs.flatMap fun b => [true, b]) ++ (false :: ys) = quote xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.flatMap_cons, quote, List.cons_append, List.nil_append]
    exact congrArg (fun l => true :: b :: l) ih

lemma update_nil_eq {α : Type} [DecidableEq α] {β : α → Type} (k₀ : α) :
    Function.update (fun a : α => ([] : List (β a))) k₀ [] = fun _ => [] := by
  funext k
  by_cases h : k = k₀
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h]

noncomputable def fanout :
    TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str)
      (fun s => encodePair id id (f1 s, f2 s)) where
  tm := tm M N
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time :=
    let sb1 := X + M.time * C (tmGrowth M.tm)
    let sb2 := X + N.time * C (tmGrowth N.tm)
    2 * X + M.time + N.time + 2 * sb1 + 2 * sb2 + 8
  outputsFun s := by
    let hM := M.outputsFun s
    let hN := N.outputsFun s
    have tM : Trace M.tm.step hM.steps (initList M.tm (s.map M.inputAlphabet.symm))
        (haltList M.tm ((f1 s).map M.outputAlphabet.symm)) := Trace.of_iterate hM.evals_in_steps
    have tN : Trace N.tm.step hN.steps (initList N.tm (s.map N.inputAlphabet.symm))
        (haltList N.tm ((f2 s).map N.outputAlphabet.symm)) := Trace.of_iterate hN.evals_in_steps
    have hc := copy_run M N s []
    rw [← init_eq_ph0] at hc
    simp only [List.append_nil] at hc
    have hd := dist_run M N s.reverse [] []
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil,
      update_nil_eq] at hd
    have h1 := (left M N (Function.update (fun _ => []) N.tm.k₀ (s.map N.inputAlphabet.symm))).trace
      M.tm.m (tm M N).m (fun l => by
        simp only [tm, code]
        exact left_stmt_indep M N _ _ _) tM
    rw [left_halt_eq_right_init] at h1
    have h2 := (right M N (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))).trace
      N.tm.m (tm M N).m (fun l => by
        simp only [tm, code]
        exact right_stmt_indep M N _ _ _) tN
    rw [right_halt_eq_ph2] at h2
    have hdr2 := drain2_run M N
      (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))
      ((f2 s).map N.outputAlphabet.symm) []
    simp only [List.length_map, List.map_map, Function.comp_def, Equiv.apply_symm_apply,
      List.map_id', List.append_nil] at hdr2
    have hem2 := emit2_run M N
      (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))
      (f2 s).reverse []
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hem2
    have hdr1 := drain1_run M N ((f1 s).map M.outputAlphabet.symm) [] (false :: f2 s)
    simp only [List.length_map, List.map_map, Function.comp_def, Equiv.apply_symm_apply,
      List.map_id', List.append_nil] at hdr1
    have hem1 := emit1_run M N (f1 s).reverse (false :: f2 s)
    simp only [List.length_reverse, List.reverse_reverse, quote_eq_flatMap] at hem1
    have hfull := ((((((hc.trans hd).trans h1).trans h2).trans hdr2).trans hem2).trans hdr1).trans hem1
    dsimp only [FinTM2.Γ, FinTM2.k₀, FinTM2.k₁, tm, inpKey, outKey, Γ, encodePair, id_eq]
    rw [show List.map (Equiv.refl Bool).invFun s = s from list_map_equiv_refl s]
    rw [show List.map (Equiv.refl Bool).invFun (quote (f1 s) ++ f2 s) = quote (f1 s) ++ f2 s from
      list_map_equiv_refl _]
    refine ⟨⟨_, hfull.iterate_eq⟩, ?_⟩
    have hl1 : ((f1 s).map M.outputAlphabet.symm).length ≤
        (s.map M.inputAlphabet.symm).length + (M.time.eval s.length) * tmGrowth M.tm :=
      finTM2_output_length M.tm hM
    have hl2 : ((f2 s).map N.outputAlphabet.symm).length ≤
        (s.map N.inputAlphabet.symm).length + (N.time.eval s.length) * tmGrowth N.tm :=
      finTM2_output_length N.tm hN
    simp only [List.length_map] at hl1 hl2
    have hm1 := hM.steps_le_m
    have hm2 := hN.steps_le_m
    simp only [id_eq] at hm1 hm2
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C, id_eq]
    omega

end TM2Fanout

end TM2Plumbing

/-! ### Part 2: Classical PolyTime Combinators for Seq -/

section PolySeq

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime

def incLastT : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some b, [])
    | some prev => (some b, [true, prev, false])
  finish q := match q with
    | none => []
    | some _ => [true, true, false, true, false, false]

def incLastAux : Option Bool → List Bool → List Bool
  | none, [] => []
  | none, b :: xs => incLastAux (some b) xs
  | some _, [] => [true, false]
  | some prev, b :: xs => prev :: incLastAux (some b) xs

lemma incLastT_run (q : Option Bool) (xs : List Bool) :
    incLastT.run q xs = encodeList encodeBool (incLastAux q xs) := by
  induction xs generalizing q with
  | nil =>
    cases q <;> simp [Transducer.run, incLastT, incLastAux, encodeList, encodeBool, quote]
  | cons b xs ih =>
    cases q with
    | none => exact ih (some b)
    | some prev =>
      change [true, prev, false] ++ incLastT.run (some b) xs = _
      rw [ih (some b)]
      rfl

noncomputable def incLastProgram : PolyProgram id id (incLastAux none) :=
  (incLastT.program.recode id (fun _ => rfl) (fun xs => incLastT_run none xs)).comp
    BooleanLists.unpackProgram

lemma incLastAux_some_append (prev : Bool) (xs : List Bool) :
    incLastAux (some prev) (xs ++ [false]) = prev :: (xs ++ [true, false]) := by
  induction xs generalizing prev with
  | nil => rfl
  | cons a xs ih =>
    change prev :: incLastAux (some a) (xs ++ [false]) = prev :: ((a :: xs) ++ [true, false])
    rw [ih a]
    rfl

lemma rep_append_true (k : ℕ) :
    List.replicate k true ++ [true] = true :: List.replicate k true := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

lemma incLastAux_enc (pref : List Bool) (k : ℕ) :
    incLastAux none (pref ++ encNat k) = pref ++ encNat (k + 1) := by
  have h1 : pref ++ encNat k = (pref ++ List.replicate k true) ++ [false] := by
    simp [encNat, List.append_assoc]
  have h2 : pref ++ encNat (k + 1) = (pref ++ List.replicate k true) ++ [true, false] := by
    simp only [encNat, List.replicate_succ]
    rw [← rep_append_true k, List.append_assoc, List.append_assoc]
    rfl
  rw [h1, h2]
  cases h : pref ++ List.replicate k true with
  | nil => rfl
  | cons b rest =>
    change incLastAux (some b) (rest ++ [false]) = b :: (rest ++ [true, false])
    exact incLastAux_some_append b rest

def qBit (b : Bool) : List Bool := [true, true, true, b, true, false]
def endSeg : List Bool := [false]

def parseSeqT : Transducer where
  Q := Fin 9
  initial := 0
  next q b :=
    if q = 0 then (if b then (1, []) else (6, endSeg ++ endSeg ++ endSeg))
    else if q = 1 then (if b then (0, qBit true) else (2, endSeg))
    else if q = 2 then (if b then (3, []) else (6, endSeg ++ endSeg))
    else if q = 3 then (if b then (2, qBit true) else (4, endSeg))
    else if q = 4 then (if b then (5, []) else (6, endSeg))
    else if q = 5 then (4, qBit b)
    else if q = 6 then (if b then (6, qBit true) else (7, endSeg))
    else if q = 7 then (if b then (7, qBit true) else (8, endSeg))
    else (8, qBit b)
  finish q :=
    if q = 0 ∨ q = 1 then endSeg ++ endSeg ++ endSeg ++ endSeg ++ endSeg ++ endSeg
    else if q = 2 ∨ q = 3 then endSeg ++ endSeg ++ endSeg ++ endSeg ++ endSeg
    else if q = 4 ∨ q = 5 then endSeg ++ endSeg ++ endSeg ++ endSeg
    else if q = 6 then endSeg ++ endSeg ++ endSeg
    else if q = 7 then endSeg ++ endSeg
    else endSeg

def consHead (b : Bool) : List (List Bool) → List (List Bool)
  | [] => [[b]]
  | hd :: tl => (b :: hd) :: tl

lemma consHead_ne_nil (b : Bool) (L : List (List Bool)) : consHead b L ≠ [] := by
  cases L <;> simp [consHead]

def parseSeqAux : Fin 9 → List Bool → List (List Bool)
  | 0, [] => [[], [], [], [], [], []]
  | 1, [] => [[], [], [], [], [], []]
  | 2, [] => [[], [], [], [], []]
  | 3, [] => [[], [], [], [], []]
  | 4, [] => [[], [], [], []]
  | 5, [] => [[], [], [], []]
  | 6, [] => [[], [], []]
  | 7, [] => [[], []]
  | 8, [] => [[]]
  | 0, true :: xs => parseSeqAux 1 xs
  | 0, false :: xs => [] :: [] :: [] :: parseSeqAux 6 xs
  | 1, true :: xs => consHead true (parseSeqAux 0 xs)
  | 1, false :: xs => [] :: parseSeqAux 2 xs
  | 2, true :: xs => parseSeqAux 3 xs
  | 2, false :: xs => [] :: [] :: parseSeqAux 6 xs
  | 3, true :: xs => consHead true (parseSeqAux 2 xs)
  | 3, false :: xs => [] :: parseSeqAux 4 xs
  | 4, true :: xs => parseSeqAux 5 xs
  | 4, false :: xs => [] :: parseSeqAux 6 xs
  | 5, b :: xs => consHead b (parseSeqAux 4 xs)
  | 6, true :: xs => consHead true (parseSeqAux 6 xs)
  | 6, false :: xs => [] :: parseSeqAux 7 xs
  | 7, true :: xs => consHead true (parseSeqAux 7 xs)
  | 7, false :: xs => [] :: parseSeqAux 8 xs
  | 8, b :: xs => consHead b (parseSeqAux 8 xs)

lemma parseSeqAux_ne_nil (q : Fin 9) (xs : List Bool) : parseSeqAux q xs ≠ [] := by
  induction xs generalizing q with
  | nil => fin_cases q <;> simp [parseSeqAux]
  | cons b xs ih => fin_cases q <;> cases b <;> simp [parseSeqAux, consHead_ne_nil, ih]

lemma quote_encodeList_cons (b : Bool) (xs : List Bool) :
    quote (encodeList encodeBool (b :: xs)) = qBit b ++ quote (encodeList encodeBool xs) := by
  simp [encodeList, encodeBool, quote, qBit]

lemma encList_cons (hd : List Bool) (tl : List (List Bool)) :
    encodeList (encodeList encodeBool) (hd :: tl) =
      quote (encodeList encodeBool hd) ++ encodeList (encodeList encodeBool) tl := rfl

lemma run_consHead (b : Bool) (L : List (List Bool)) (hne : L ≠ []) :
    encodeList (encodeList encodeBool) (consHead b L) =
      qBit b ++ encodeList (encodeList encodeBool) L := by
  cases L with
  | nil => exact absurd rfl hne
  | cons hd tl =>
    simp only [consHead, encList_cons, quote_encodeList_cons, List.append_assoc]

lemma parseSeqT_run (q : Fin 9) (xs : List Bool) :
    parseSeqT.run q xs = encodeList (encodeList encodeBool) (parseSeqAux q xs) := by
  induction xs generalizing q with
  | nil => fin_cases q <;> simp [Transducer.run, parseSeqT, parseSeqAux, endSeg, encodeList, quote]
  | cons b xs ih =>
    fin_cases q <;> dsimp only
    · cases b
      · change (endSeg ++ endSeg ++ endSeg) ++ parseSeqT.run (6 : Fin 9) xs = _
        rw [ih 6]; dsimp only [parseSeqAux]; rfl
      · change [] ++ parseSeqT.run (1 : Fin 9) xs = _
        rw [ih 1]; dsimp only [parseSeqAux]; rfl
    · cases b
      · change endSeg ++ parseSeqT.run (2 : Fin 9) xs = _
        rw [ih 2]; dsimp only [parseSeqAux]; rfl
      · change qBit true ++ parseSeqT.run (0 : Fin 9) xs = _
        rw [ih 0]; dsimp only [parseSeqAux]; rw [run_consHead _ _ (parseSeqAux_ne_nil 0 xs)]
    · cases b
      · change (endSeg ++ endSeg) ++ parseSeqT.run (6 : Fin 9) xs = _
        rw [ih 6]; dsimp only [parseSeqAux]; rfl
      · change [] ++ parseSeqT.run (3 : Fin 9) xs = _
        rw [ih 3]; dsimp only [parseSeqAux]; rfl
    · cases b
      · change endSeg ++ parseSeqT.run (4 : Fin 9) xs = _
        rw [ih 4]; dsimp only [parseSeqAux]; rfl
      · change qBit true ++ parseSeqT.run (2 : Fin 9) xs = _
        rw [ih 2]; dsimp only [parseSeqAux]; rw [run_consHead _ _ (parseSeqAux_ne_nil 2 xs)]
    · cases b
      · change endSeg ++ parseSeqT.run (6 : Fin 9) xs = _
        rw [ih 6]; dsimp only [parseSeqAux]; rfl
      · change [] ++ parseSeqT.run (5 : Fin 9) xs = _
        rw [ih 5]; dsimp only [parseSeqAux]; rfl
    · change qBit b ++ parseSeqT.run (4 : Fin 9) xs = _
      rw [ih 4]; dsimp only [parseSeqAux]; rw [run_consHead _ _ (parseSeqAux_ne_nil 4 xs)]
    · cases b
      · change endSeg ++ parseSeqT.run (7 : Fin 9) xs = _
        rw [ih 7]; dsimp only [parseSeqAux]; rfl
      · change qBit true ++ parseSeqT.run (6 : Fin 9) xs = _
        rw [ih 6]; dsimp only [parseSeqAux]; rw [run_consHead _ _ (parseSeqAux_ne_nil 6 xs)]
    · cases b
      · change endSeg ++ parseSeqT.run (8 : Fin 9) xs = _
        rw [ih 8]; dsimp only [parseSeqAux]; rfl
      · change qBit true ++ parseSeqT.run (7 : Fin 9) xs = _
        rw [ih 7]; dsimp only [parseSeqAux]; rw [run_consHead _ _ (parseSeqAux_ne_nil 7 xs)]
    · change qBit b ++ parseSeqT.run (8 : Fin 9) xs = _
      rw [ih 8]; dsimp only [parseSeqAux]; rw [run_consHead _ _ (parseSeqAux_ne_nil 8 xs)]

lemma parseSeqAux_8 (b2 : List Bool) :
    parseSeqAux 8 b2 = [b2] := by
  induction b2 with
  | nil => rfl
  | cons b b2 ih =>
    change consHead b (parseSeqAux 8 b2) = [b :: b2]
    rw [ih]; rfl

lemma parseSeqAux_7 (l2 : ℕ) (b2 : List Bool) :
    parseSeqAux 7 (List.replicate l2 true ++ false :: b2) = [List.replicate l2 true, b2] := by
  induction l2 with
  | zero =>
    change [] :: parseSeqAux 8 b2 = [[], b2]
    rw [parseSeqAux_8]
  | succ l2 ih =>
    change consHead true (parseSeqAux 7 (List.replicate l2 true ++ false :: b2)) =
      [true :: List.replicate l2 true, b2]
    rw [ih]; rfl

lemma parseSeqAux_6 (w2 : ℕ) (rest : List Bool) :
    parseSeqAux 6 (List.replicate w2 true ++ false :: rest) =
      List.replicate w2 true :: parseSeqAux 7 rest := by
  induction w2 with
  | zero => rfl
  | succ w2 ih =>
    change consHead true (parseSeqAux 6 (List.replicate w2 true ++ false :: rest)) =
      (true :: List.replicate w2 true) :: parseSeqAux 7 rest
    rw [ih]; rfl

lemma parseSeqAux_4 (b1 rest2 : List Bool) :
    parseSeqAux 4 (quote b1 ++ rest2) = b1 :: parseSeqAux 6 rest2 := by
  induction b1 with
  | nil => rfl
  | cons b b1 ih =>
    change consHead b (parseSeqAux 4 (quote b1 ++ rest2)) = (b :: b1) :: parseSeqAux 6 rest2
    rw [ih]; rfl

lemma parseSeqAux_2 (l1 : ℕ) (b1 rest2 : List Bool) :
    parseSeqAux 2 (quote (encNat l1 ++ b1) ++ rest2) =
      List.replicate l1 true :: parseSeqAux 4 (quote b1 ++ rest2) := by
  induction l1 with
  | zero => rfl
  | succ l1 ih =>
    change consHead true (parseSeqAux 2 (quote (encNat l1 ++ b1) ++ rest2)) =
      (true :: List.replicate l1 true) :: parseSeqAux 4 (quote b1 ++ rest2)
    rw [ih]; rfl

lemma parseSeqAux_0 (w1 : ℕ) (s1 rest2 : List Bool) :
    parseSeqAux 0 (quote (encNat w1 ++ s1) ++ rest2) =
      List.replicate w1 true :: parseSeqAux 2 (quote s1 ++ rest2) := by
  induction w1 with
  | zero => rfl
  | succ w1 ih =>
    change consHead true (parseSeqAux 0 (quote (encNat w1 ++ s1) ++ rest2)) =
      (true :: List.replicate w1 true) :: parseSeqAux 2 (quote s1 ++ rest2)
    rw [ih]; rfl

lemma parseSeqAux_eq {w1 w2 : ℕ} (c1 : List (Instr w1)) (c2 : List (Instr w2)) :
    parseSeqAux 0 (quote (encNat w1 ++ encLayer c1) ++ (encNat w2 ++ encLayer c2)) =
      [List.replicate w1 true, List.replicate c1.length true, (c1.map encInstr).flatten,
       List.replicate w2 true, List.replicate c2.length true, (c2.map encInstr).flatten] := by
  simp only [encLayer, encStr, List.length_map]
  rw [parseSeqAux_0, parseSeqAux_2, parseSeqAux_4]
  simp only [encNat, List.append_assoc, List.singleton_append]
  rw [parseSeqAux_6, parseSeqAux_7]

noncomputable def parseSeqProgram : PolyProgram id enc (parseSeqAux 0) :=
  parseSeqT.program.recode id (fun _ => rfl) (fun s => parseSeqT_run 0 s)

def seqBody (L : List (List Bool)) : List Bool :=
  let w1 := L[0]?.getD []
  let l1 := L[1]?.getD []
  let b1 := L[2]?.getD []
  let w2 := L[3]?.getD []
  let l2 := L[4]?.getD []
  let b2 := L[5]?.getD []
  let wMax := if w1.length ≤ w2.length then w2 else w1
  wMax ++ [false] ++ l1 ++ l2 ++ [false] ++ b1 ++ b2

@[fun_prop] lemma seqBody_poly : Poly seqBody := by
  unfold seqBody
  fun_prop

lemma seqBody_eq {w1 w2 : ℕ} (c1 : List (Instr w1)) (c2 : List (Instr w2)) :
    seqBody [List.replicate w1 true, List.replicate c1.length true, (c1.map encInstr).flatten,
        List.replicate w2 true, List.replicate c2.length true, (c2.map encInstr).flatten] =
      encNat (max w1 w2) ++
        encNat (c1.length + c2.length) ++
        (c1.map encInstr).flatten ++
        (c2.map encInstr).flatten := by
  unfold seqBody
  dsimp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [List.length_replicate]
  have hw : (if w1 ≤ w2 then List.replicate w2 true else List.replicate w1 true) =
      List.replicate (max w1 w2) true := by
    by_cases h : w1 ≤ w2
    · simp [h]
    · simp [h, Nat.max_eq_left (Nat.le_of_not_ge h)]
  rw [hw]
  simp only [encNat]
  rw [List.replicate_add]
  simp only [List.append_assoc]

noncomputable def seqPostProgram : PolyProgram id id (seqBody ∘ parseSeqAux 0) :=
  parseSeqProgram.comp (seqBody_poly.program.comp BooleanLists.unpackProgram)

end PolySeq

/-! ### Part 3: Quantum Circuit Composition, Shifting, and Padding Isometry -/

section QuantumSeq

lemma embedOp_mul {k n : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    let agree (u : Qubits n) : Prop := ∀ a : Fin n, a ∉ Set.range w → y a = u a
    let mkU (v : Qubits k) : Qubits n := fun a => if h : ∃ i, w i = a then v h.choose else y a
    have hmkU_w : ∀ v i, mkU v (w i) = v i := by
      intro v i
      have hex : ∃ j, w j = w i := ⟨i, rfl⟩
      simp only [mkU, dif_pos hex]
      congr 1
      exact w.injective hex.choose_spec
    have hmkU_off : ∀ v, agree (mkU v) := by
      intro v a ha
      have hneg : ¬ ∃ i, w i = a := by simpa [Set.mem_range] using ha
      simp only [mkU, dif_neg hneg]
    have hmkU_id : ∀ u, agree u → mkU (fun i => u (w i)) = u := by
      intro u hu
      funext a
      by_cases hex : ∃ i, w i = a
      · rcases hex with ⟨i, rfl⟩
        exact hmkU_w (fun i => u (w i)) i
      · simp only [mkU, dif_neg hex]
        exact hu a (fun ⟨i, hi⟩ => hex ⟨i, hi⟩)
    have hsum1 : (∑ u : Qubits n,
          (if agree u then A (y ∘ w) (u ∘ w) else 0) *
          (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0)) =
        ∑ u ∈ Finset.univ.filter agree, A (y ∘ w) (u ∘ w) * B (u ∘ w) (z ∘ w) := by
      have hrew : (∑ u : Qubits n,
            (if agree u then A (y ∘ w) (u ∘ w) else 0) *
            (if ∀ a, a ∉ Set.range w → u a = z a then B (u ∘ w) (z ∘ w) else 0)) =
          ∑ u : Qubits n, if agree u then A (y ∘ w) (u ∘ w) * B (u ∘ w) (z ∘ w) else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        by_cases hua : agree u
        · have huz : ∀ a, a ∉ Set.range w → u a = z a := fun a ha => (hua a ha).symm.trans (hyz a ha)
          rw [if_pos hua, if_pos huz, if_pos hua]
        · rw [if_neg hua, zero_mul, if_neg hua]
      rw [hrew, ← Finset.sum_filter]
    rw [hsum1]
    refine Finset.sum_nbij' mkU (fun (u : Qubits n) (i : Fin k) => u (w i)) ?_ ?_ ?_ ?_ ?_
    · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmkU_off v⟩
    · intro u _; exact Finset.mem_univ _
    · intro v _; funext i; exact hmkU_w v i
    · intro u hu; exact hmkU_id u (Finset.mem_filter.mp hu).2
    · intro v _
      have hcomp : mkU v ∘ w = v := by funext i; exact hmkU_w v i
      rw [hcomp]
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    split_ifs with h1 h2
    · exfalso; exact hyz fun a ha => (h1 a ha).trans (h2 a ha)
    · simp
    · simp
    · simp

lemma embedOp_conjTranspose {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M.conjTranspose w = (embedOp M w).conjTranspose := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso; exact h2 fun a ha => (h1 a ha).symm
  · exfalso; exact h1 fun a ha => (h3 a ha).symm
  · simp

lemma embedOp_mem_unitaryGroup {k n : ℕ} {M : Matrix (Qubits k) (Qubits k) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  change embedOp M w * (embedOp M w).conjTranspose = 1
  rw [← embedOp_conjTranspose, ← embedOp_mul]
  change M * M.conjTranspose = 1 at hM
  rw [hM, embedOp_one]

def q1Equiv : Qubits 1 ≃ Bool where
  toFun b := b 0
  invFun b _ := b
  left_inv b := by ext i; fin_cases i; rfl
  right_inv _ := rfl

def q2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun b := (b 0, b 1)
  invFun p := ![p.1, p.2]
  left_inv b := by ext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl

lemma ofMatrix1_eq_submatrix (M : Matrix Bool Bool ℂ) :
    (Gate.ofMatrix1 M).mat = M.submatrix q1Equiv q1Equiv := rfl

lemma ofMatrix2_eq_submatrix (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    (Gate.ofMatrix2 M).mat = M.submatrix q2Equiv q2Equiv := rfl

lemma submatrix_equiv_mul {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (A B : Matrix β β ℂ) :
    A.submatrix e e * B.submatrix e e = (A * B).submatrix e e := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

lemma submatrix_equiv_one {α β : Type} [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    (1 : Matrix β β ℂ).submatrix e e = 1 := by
  ext x y
  simp [Matrix.one_apply, e.apply_eq_iff_eq]

lemma submatrix_equiv_conjTranspose {α β : Type} (e : α ≃ β) (A : Matrix β β ℂ) :
    (A.submatrix e e).conjTranspose = A.conjTranspose.submatrix e e := rfl

lemma hadamard_conjTranspose : hadamard.conjTranspose = hadamard := by
  ext a b; cases a <;> cases b <;> simp [hadamard]

lemma pauliX_conjTranspose : pauliX.conjTranspose = pauliX := by
  ext a b; cases a <;> cases b <;> simp [pauliX]

lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply]

lemma phaseS_unitary : phaseS * phaseS.conjTranspose = 1 := by
  ext a b; cases a <;> cases b <;> simp [phaseS, Matrix.mul_apply]

lemma gateT_unitary : gateT * gateT.conjTranspose = 1 := by
  ext a b
  cases a <;> cases b <;> simp [gateT, Matrix.mul_apply]
  rw [← Complex.exp_conj]
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, ← Complex.exp_add]
  have h0 : Complex.I * ↑Real.pi / 4 + -Complex.I * ↑Real.pi / (4 : ℂ) = 0 := by ring
  rw [h0, Complex.exp_zero]

lemma cnot_conjTranspose : cnot.conjTranspose = cnot := by
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> simp [cnot]

lemma cnot_mul_self : cnot * cnot = 1 := by
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type]

lemma instr_mem_unitaryGroup {n : ℕ} (g : Instr n) :
    embedOp (instrApp g).gate.mat (instrApp g).wires ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  apply embedOp_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff]
  change (instrApp g).gate.mat * (instrApp g).gate.mat.conjTranspose = 1
  cases g with
  | h i =>
    change hadamard.submatrix q1Equiv q1Equiv * (hadamard.submatrix q1Equiv q1Equiv).conjTranspose = 1
    rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, hadamard_conjTranspose,
      hadamard_mul_self, submatrix_equiv_one]
  | s i =>
    change phaseS.submatrix q1Equiv q1Equiv * (phaseS.submatrix q1Equiv q1Equiv).conjTranspose = 1
    rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, phaseS_unitary, submatrix_equiv_one]
  | t i =>
    change gateT.submatrix q1Equiv q1Equiv * (gateT.submatrix q1Equiv q1Equiv).conjTranspose = 1
    rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, gateT_unitary, submatrix_equiv_one]
  | x i =>
    change pauliX.submatrix q1Equiv q1Equiv * (pauliX.submatrix q1Equiv q1Equiv).conjTranspose = 1
    rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, pauliX_conjTranspose,
      pauliX_mul_self, submatrix_equiv_one]
  | cnot i j hij =>
    change cnot.submatrix q2Equiv q2Equiv * (cnot.submatrix q2Equiv q2Equiv).conjTranspose = 1
    rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, cnot_conjTranspose,
      cnot_mul_self, submatrix_equiv_one]

lemma circUnitary_mem_unitaryGroup {n : ℕ} (c : List (Instr n)) :
    circUnitary c ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  induction c with
  | nil =>
    simp only [circUnitary, Circuit.unitary, List.map_nil, List.reverse_nil, List.prod_nil]
    exact one_mem _
  | cons g c ih =>
    simp only [circUnitary, Circuit.unitary, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one] at ih ⊢
    exact mul_mem ih (instr_mem_unitaryGroup g)

lemma circUnitary_append {n : ℕ} (c₁ c₂ : List (Instr n)) :
    circUnitary (c₁ ++ c₂) = circUnitary c₂ * circUnitary c₁ := by
  simp [circUnitary, Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

lemma act_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  apply WithLp.ofLp_injective
  simp [act, Matrix.mulVec_mulVec]

lemma encInstr_mapInstr_shift0 {w1 w : ℕ} (hle : w1 ≤ w) (g : Instr w1) :
    encInstr (mapInstr (shiftEmb 0 w1 w (by omega)) g) = encInstr g := by
  cases g <;> simp [mapInstr, shiftEmb, encInstr]

lemma map_encInstr_mapCirc_shift0 {w1 w : ℕ} (hle : w1 ≤ w) (c : List (Instr w1)) :
    (mapCirc (shiftEmb 0 w1 w (by omega)) c).map encInstr = c.map encInstr := by
  simp only [mapCirc, List.map_map, Function.comp_def, encInstr_mapInstr_shift0 hle]

def padRestrict {w1 w : ℕ} (hle : w1 ≤ w) (y : Qubits w) : Qubits w1 :=
  fun i => y (shiftEmb 0 w1 w (by omega) i)

def padEmbedVec {w1 w : ℕ} (hle : w1 ≤ w) (v : EuclideanSpace ℂ (Qubits w1)) :
    EuclideanSpace ℂ (Qubits w) :=
  WithLp.toLp 2 fun y =>
    if ∀ a : Fin w, w1 ≤ a.val → y a = false then v (padRestrict hle y) else 0

lemma padRestrict_padTo {w1 w : ℕ} (hle : w1 ≤ w) (z : Qubits w1) :
    padRestrict hle (padTo w z) = z := by
  funext i
  simp [padRestrict, shiftEmb, padTo, i.isLt]

lemma padTo_padRestrict {w1 w : ℕ} (hle : w1 ≤ w) (y : Qubits w)
    (hy : ∀ a : Fin w, w1 ≤ a.val → y a = false) :
    padTo w (padRestrict hle y) = y := by
  funext a
  by_cases ha : a.val < w1
  · simp [padTo, padRestrict, shiftEmb, ha]
  · have hge : w1 ≤ a.val := Nat.le_of_not_lt ha
    simp [padTo, ha, hy a hge]

lemma padTo_zero_hi {w1 w : ℕ} (_hle : w1 ≤ w) (z : Qubits w1) (a : Fin w) (ha : w1 ≤ a.val) :
    padTo w z a = false := by
  simp [padTo, show ¬ a.val < w1 by omega]

lemma padEmbedVec_sub {w1 w : ℕ} (hle : w1 ≤ w) (u v : EuclideanSpace ℂ (Qubits w1)) :
    padEmbedVec hle (u - v) = padEmbedVec hle u - padEmbedVec hle v := by
  apply WithLp.ofLp_injective
  funext y
  simp only [padEmbedVec, PiLp.sub_apply, WithLp.ofLp_toLp]
  split_ifs <;> ring

lemma norm_padEmbedVec {w1 w : ℕ} (hle : w1 ≤ w) (v : EuclideanSpace ℂ (Qubits w1)) :
    ‖padEmbedVec hle v‖ = ‖v‖ := by
  have hsq : ‖padEmbedVec hle v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [padEmbedVec, WithLp.ofLp_toLp]
    let P (y : Qubits w) : Prop := ∀ a : Fin w, w1 ≤ a.val → y a = false
    have hfilt : (∑ y : Qubits w, ‖if P y then WithLp.ofLp v (padRestrict hle y) else 0‖ ^ 2) =
        ∑ y ∈ Finset.univ.filter P, ‖WithLp.ofLp v (padRestrict hle y)‖ ^ 2 := by
      have hrew : (∑ y : Qubits w, ‖if P y then WithLp.ofLp v (padRestrict hle y) else 0‖ ^ 2) =
          ∑ y : Qubits w, if P y then ‖WithLp.ofLp v (padRestrict hle y)‖ ^ 2 else 0 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
      rw [hrew, ← Finset.sum_filter]
    rw [hfilt]
    refine Finset.sum_nbij' (padRestrict hle) (padTo w) ?_ ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro z _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha => padTo_zero_hi hle z a ha⟩
    · intro y hy; exact padTo_padRestrict hle y (Finset.mem_filter.mp hy).2
    · intro z _; exact padRestrict_padTo hle z
    · intro _ _; rfl
  nlinarith [norm_nonneg (padEmbedVec hle v), norm_nonneg v]

lemma padEmbedVec_embedVec {A : Type} [Fintype A] {m w1 w : ℕ} (hm : m ≤ w1) (hle : w1 ≤ w)
    (code : A → Qubits m) (φ : EuclideanSpace ℂ A) :
    embedVec (fun a => padTo w (code a)) φ =
      padEmbedVec hle (embedVec (fun a => padTo w1 (code a)) φ) := by
  apply WithLp.ofLp_injective
  funext y
  simp only [embedVec, padEmbedVec, WithLp.ofLp_toLp]
  by_cases hy : ∀ a : Fin w, w1 ≤ a.val → y a = false
  · rw [if_pos hy]
    refine Finset.sum_congr rfl fun a _ => ?_
    have heq : (padTo w (code a) = y) ↔ (padTo w1 (code a) = padRestrict hle y) := by
      constructor
      · intro h; subst h
        funext i
        have hi : i.val < w1 := i.isLt
        by_cases hm' : i.val < m
        · simp [padRestrict, shiftEmb, padTo, hm']
        · simp [padRestrict, shiftEmb, padTo, hm']
      · intro h
        funext b
        by_cases hb1 : b.val < w1
        · have hb := congrFun h ⟨b.val, hb1⟩
          by_cases hbm : b.val < m
          · simpa [padTo, padRestrict, shiftEmb, hbm] using hb
          · simpa [padTo, padRestrict, shiftEmb, hbm] using hb
        · have hge : w1 ≤ b.val := Nat.le_of_not_lt hb1
          have hbm : ¬ b.val < m := by omega
          simp [padTo, hbm, hy b hge]
    simp [heq]
  · rw [if_neg hy]
    push Not at hy
    rcases hy with ⟨a, ha1, hya⟩
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : padTo w (code x) ≠ y := by
      intro h
      have := congrFun h a
      have ham : ¬ a.val < m := by omega
      simp [padTo, ham] at this
      exact hya this
    simp [hne]

lemma act_embedOp_shift_padEmbedVec {k w1 w : ℕ} (hle : w1 ≤ w)
    (M : Matrix (Qubits k) (Qubits k) ℂ) (u : Fin k ↪ Fin w1)
    (v : EuclideanSpace ℂ (Qubits w1)) :
    act (embedOp M (u.trans (shiftEmb 0 w1 w (by omega)))) (padEmbedVec hle v) =
      padEmbedVec hle (act (embedOp M u) v) := by
  let e := shiftEmb 0 w1 w (by omega)
  let u' := u.trans e
  apply WithLp.ofLp_injective
  funext y
  simp only [act, padEmbedVec, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
  by_cases hy : ∀ a : Fin w, w1 ≤ a.val → y a = false
  · rw [if_pos hy]
    let P (z : Qubits w) : Prop := ∀ a : Fin w, w1 ≤ a.val → z a = false
    have hfilt : (∑ z : Qubits w, embedOp M u' y z *
          (if P z then WithLp.ofLp v (padRestrict hle z) else 0)) =
        ∑ z ∈ Finset.univ.filter P, embedOp M u' y z * WithLp.ofLp v (padRestrict hle z) := by
      have hrew : (∑ z : Qubits w, embedOp M u' y z *
            (if P z then WithLp.ofLp v (padRestrict hle z) else 0)) =
          ∑ z : Qubits w, if P z then embedOp M u' y z * WithLp.ofLp v (padRestrict hle z) else 0 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        split_ifs <;> simp
      rw [hrew, ← Finset.sum_filter]
    rw [hfilt]
    refine Finset.sum_nbij' (padRestrict hle) (padTo w) ?_ ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro z _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha => padTo_zero_hi hle z a ha⟩
    · intro z hz; exact padTo_padRestrict hle z (Finset.mem_filter.mp hz).2
    · intro z _; exact padRestrict_padTo hle z
    · intro z hz
      have hzp : P z := (Finset.mem_filter.mp hz).2
      simp only [embedOp, Matrix.of_apply]
      have hiff : (∀ a : Fin w, a ∉ Set.range u' → y a = z a) ↔
          (∀ b : Fin w1, b ∉ Set.range u → padRestrict hle y b = padRestrict hle z b) := by
        constructor
        · intro h b hb
          apply h (e b)
          rintro ⟨i, hi⟩
          exact hb ⟨i, e.injective hi⟩
        · intro h a ha
          by_cases ha1 : a.val < w1
          · have hae : e ⟨a.val, ha1⟩ = a := by ext; simp [e, shiftEmb]
            have hnb : (⟨a.val, ha1⟩ : Fin w1) ∉ Set.range u := by
              rintro ⟨i, hi⟩
              apply ha
              exact ⟨i, by simp [u', hi, hae]⟩
            have hres := h ⟨a.val, ha1⟩ hnb
            dsimp only [padRestrict] at hres
            change y (e ⟨a.val, ha1⟩) = z (e ⟨a.val, ha1⟩) at hres
            rw [hae] at hres
            exact hres
          · have hge : w1 ≤ a.val := Nat.le_of_not_lt ha1
            rw [hy a hge, hzp a hge]
      have hycomp : y ∘ u' = padRestrict hle y ∘ u := rfl
      have hzcomp : z ∘ u' = padRestrict hle z ∘ u := rfl
      by_cases h1 : ∀ a : Fin w, a ∉ Set.range u' → y a = z a
      · rw [if_pos h1, if_pos (hiff.mp h1), hycomp, hzcomp]
      · rw [if_neg h1, if_neg (mt hiff.mpr h1)]
  · rw [if_neg hy]
    push Not at hy
    rcases hy with ⟨a, ha1, hya⟩
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hza : ∀ b : Fin w, w1 ≤ b.val → z b = false
    · have ha_range : a ∉ Set.range u' := by
        rintro ⟨i, hi⟩
        have hlt : (u' i).val < w1 := by simp [u', e, shiftEmb, (u i).isLt]
        omega
      have hne : ¬ (∀ b : Fin w, b ∉ Set.range u' → y b = z b) := by
        intro h
        exact hya ((h a ha_range).trans (hza a ha1))
      rw [if_pos hza]
      simp only [embedOp, Matrix.of_apply]
      rw [if_neg hne, zero_mul]
    · rw [if_neg hza, mul_zero]

lemma instrApp_mapInstr_shift {w1 w : ℕ} (hle : w1 ≤ w) (g : Instr w1) :
    embedOp (instrApp (mapInstr (shiftEmb 0 w1 w (by omega)) g)).gate.mat
        (instrApp (mapInstr (shiftEmb 0 w1 w (by omega)) g)).wires =
      embedOp (instrApp g).gate.mat
        ((instrApp g).wires.trans (shiftEmb 0 w1 w (by omega))) := by
  cases g with
  | h i => rfl
  | s i => rfl
  | t i => rfl
  | x i => rfl
  | cnot i j hij =>
    congr 1
    ext a
    fin_cases a <;> rfl

lemma act_circUnitary_mapCirc_shift {w1 w : ℕ} (hle : w1 ≤ w) (c : List (Instr w1))
    (v : EuclideanSpace ℂ (Qubits w1)) :
    act (circUnitary (mapCirc (shiftEmb 0 w1 w (by omega)) c)) (padEmbedVec hle v) =
      padEmbedVec hle (act (circUnitary c) v) := by
  induction c generalizing v with
  | nil => simp [mapCirc, circUnitary, Circuit.unitary, act]
  | cons g c ih =>
    have hcons : mapCirc (shiftEmb 0 w1 w (by omega)) (g :: c) =
        [mapInstr (shiftEmb 0 w1 w (by omega)) g] ++
          mapCirc (shiftEmb 0 w1 w (by omega)) c := rfl
    have hc1 : g :: c = [g] ++ c := rfl
    rw [hcons, circUnitary_append, act_mul]
    have hhead : act (circUnitary [mapInstr (shiftEmb 0 w1 w (by omega)) g]) (padEmbedVec hle v) =
        padEmbedVec hle (act (circUnitary [g]) v) := by
      simp only [circUnitary, Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [instrApp_mapInstr_shift hle]
      exact act_embedOp_shift_padEmbedVec hle _ _ v
    rw [hhead, ih]
    rw [← act_mul, ← circUnitary_append, ← hc1]

end QuantumSeq

end GL2QFT_Seq_Aux

open GL2QFT_Seq_Aux

theorem solution {P : FieldData → Prop} {X M Y : FieldData → Type}
    [∀ D, Fintype (X D)] [∀ D, Fintype (M D)] [∀ D, Fintype (Y D)]
    {inW midW outW : FieldData → ℕ}
    {cin : ∀ D, X D → Qubits (inW D)} {cmid : ∀ D, M D → Qubits (midW D)}
    {cout : ∀ D, Y D → Qubits (outW D)}
    {Φ1 : ∀ D, Matrix (M D) (X D) ℂ} {Φ2 : ∀ D, Matrix (Y D) (M D) ℂ}
    (h1 : UniformlyImplementsOn P cin cmid Φ1)
    (h2 : UniformlyImplementsOn P cmid cout Φ2)
    (hbnd : ∀ D, P D → ∀ ψ : EuclideanSpace ℂ (X D),
      ‖WithLp.toLp 2 ((Φ1 D).mulVec (WithLp.ofLp ψ))‖ ≤ ‖ψ‖) :
    UniformlyImplementsOn P cin cout (fun D => Φ2 D * Φ1 D) := by
  rcases h1 with ⟨wires1, circ1, f1, c1, hf1_poly, hf1_eq, hlen1, himp1⟩
  rcases h2 with ⟨wires2, circ2, f2, c2, hf2_poly, hf2_eq, hlen2, himp2⟩
  obtain ⟨mf1⟩ := hf1_poly
  obtain ⟨mf2⟩ := hf2_poly
  let wires : FieldData → ℕ → ℕ := fun D k => max (wires1 D (k + 1)) (wires2 D (k + 1))
  let circ : ∀ D k, List (Instr (wires D k)) := fun D k =>
    mapCirc (shiftEmb 0 (wires1 D (k + 1)) (wires D k)
        (by change 0 + wires1 D (k + 1) ≤ max (wires1 D (k + 1)) (wires2 D (k + 1)); omega))
      (circ1 D (k + 1)) ++
      mapCirc (shiftEmb 0 (wires2 D (k + 1)) (wires D k)
        (by change 0 + wires2 D (k + 1) ≤ max (wires1 D (k + 1)) (wires2 D (k + 1)); omega))
      (circ2 D (k + 1))
  let f : Str → Str := (seqBody ∘ parseSeqAux 0) ∘
    (fun s => OAI.MetricKMedian.Binary.encodePair id id (f1 s, f2 s)) ∘ incLastAux none
  let N := max c1 c2
  let c := max N ((c1 + c2) * 2 ^ N)
  refine ⟨wires, circ, f, c, ?_, ?_, ?_, ?_⟩
  · exact ⟨TM2Comp.comp (TM2Comp.comp incLastProgram.stock (TM2Fanout.fanout mf1 mf2))
      seqPostProgram.stock⟩
  · intro D hD k
    change seqBody (parseSeqAux 0 (OAI.MetricKMedian.Binary.encodePair id id
        (f1 (incLastAux none (D.encData ++ encNat k)), f2 (incLastAux none (D.encData ++ encNat k))))) =
      encNat (wires D k) ++ encLayer (circ D k)
    change seqBody (parseSeqAux 0 (OAI.MetricKMedian.Binary.quote
        (f1 (incLastAux none (D.encData ++ encNat k))) ++
        f2 (incLastAux none (D.encData ++ encNat k)))) = _
    rw [incLastAux_enc, hf1_eq D hD (k + 1), hf2_eq D hD (k + 1), parseSeqAux_eq, seqBody_eq]
    simp only [wires, circ, encLayer, encStr, List.length_append, mapCirc,
      List.length_map, List.map_append, List.flatten_append, List.append_assoc]
    rw [show (List.map encInstr (List.map (mapInstr
        (shiftEmb 0 (wires1 D (k + 1)) (max (wires1 D (k + 1)) (wires2 D (k + 1))) _))
        (circ1 D (k + 1)))) =
        (circ1 D (k + 1)).map encInstr from
      map_encInstr_mapCirc_shift0 (le_max_left _ _) (circ1 D (k + 1))]
    rw [show (List.map encInstr (List.map (mapInstr
        (shiftEmb 0 (wires2 D (k + 1)) (max (wires1 D (k + 1)) (wires2 D (k + 1))) _))
        (circ2 D (k + 1)))) =
        (circ2 D (k + 1)).map encInstr from
      map_encInstr_mapCirc_shift0 (le_max_right _ _) (circ2 D (k + 1))]
  · intro D hD k
    have hl1 := hlen1 D hD (k + 1)
    have hl2 := hlen2 D hD (k + 1)
    have hbase : 1 ≤ Nat.log 2 D.q + k + 2 := by omega
    have hlog : Nat.log 2 D.q + (k + 1) + 2 ≤ 2 * (Nat.log 2 D.q + k + 2) := by omega
    have hp1 : (Nat.log 2 D.q + (k + 1) + 2) ^ c1 ≤ (2 * (Nat.log 2 D.q + k + 2)) ^ N :=
      (Nat.pow_le_pow_left hlog c1).trans (Nat.pow_le_pow_right (by omega) (le_max_left c1 c2))
    have hp2 : (Nat.log 2 D.q + (k + 1) + 2) ^ c2 ≤ (2 * (Nat.log 2 D.q + k + 2)) ^ N :=
      (Nat.pow_le_pow_left hlog c2).trans (Nat.pow_le_pow_right (by omega) (le_max_right c1 c2))
    have hpowc : (Nat.log 2 D.q + k + 2) ^ N ≤ (Nat.log 2 D.q + k + 2) ^ c :=
      Nat.pow_le_pow_right hbase (le_max_left N _)
    have hc12 : (c1 + c2) * 2 ^ N ≤ c := le_max_right N _
    have hmul1 : c1 * (Nat.log 2 D.q + (k + 1) + 2) ^ c1 ≤
        c1 * (2 ^ N * (Nat.log 2 D.q + k + 2) ^ N) := by
      rw [← mul_pow]
      exact Nat.mul_le_mul_left c1 hp1
    have hmul2 : c2 * (Nat.log 2 D.q + (k + 1) + 2) ^ c2 ≤
        c2 * (2 ^ N * (Nat.log 2 D.q + k + 2) ^ N) := by
      rw [← mul_pow]
      exact Nat.mul_le_mul_left c2 hp2
    simp only [circ, List.length_append, mapCirc, List.length_map]
    calc
      (circ1 D (k + 1)).length + (circ2 D (k + 1)).length
        ≤ c1 * (Nat.log 2 D.q + (k + 1) + 2) ^ c1 + c2 * (Nat.log 2 D.q + (k + 1) + 2) ^ c2 :=
          Nat.add_le_add hl1 hl2
      _ ≤ c1 * (2 ^ N * (Nat.log 2 D.q + k + 2) ^ N) +
          c2 * (2 ^ N * (Nat.log 2 D.q + k + 2) ^ N) := Nat.add_le_add hmul1 hmul2
      _ = ((c1 + c2) * 2 ^ N) * (Nat.log 2 D.q + k + 2) ^ N := by ring
      _ ≤ c * (Nat.log 2 D.q + k + 2) ^ c := Nat.mul_le_mul hc12 hpowc
  · intro D hD k
    obtain ⟨hin1, hmid1, himp1_k⟩ := himp1 D hD (k + 1)
    obtain ⟨hmid2, hout2, himp2_k⟩ := himp2 D hD (k + 1)
    have hle1 : wires1 D (k + 1) ≤ wires D k := le_max_left _ _
    have hle2 : wires2 D (k + 1) ≤ wires D k := le_max_right _ _
    refine ⟨hin1.trans hle1, hout2.trans hle2, ?_⟩
    intro ψ
    let c1' := mapCirc (shiftEmb 0 (wires1 D (k + 1)) (wires D k)
      (by dsimp only [wires]; omega)) (circ1 D (k + 1))
    let c2' := mapCirc (shiftEmb 0 (wires2 D (k + 1)) (wires D k)
      (by dsimp only [wires]; omega)) (circ2 D (k + 1))
    let U1' := circUnitary c1'
    let U2' := circUnitary c2'
    let φ : EuclideanSpace ℂ (M D) := WithLp.toLp 2 ((Φ1 D).mulVec (WithLp.ofLp ψ))
    have hU2' : U2' ∈ Matrix.unitaryGroup (Qubits (wires D k)) ℂ := circUnitary_mem_unitaryGroup _
    have hmul : act (circUnitary (circ D k)) (embedVec (fun x => padTo (wires D k) (cin D x)) ψ) =
        act U2' (act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ)) := by
      change act (circUnitary (c1' ++ c2')) _ = _
      rw [circUnitary_append, act_mul]
    have hΦmul : WithLp.toLp 2 ((Φ2 D * Φ1 D).mulVec (WithLp.ofLp ψ)) =
        WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ)) := by
      apply WithLp.ofLp_injective
      simp [φ, Matrix.mulVec_mulVec]
    rw [hmul, hΦmul]
    have hsplit : act U2' (act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ)) -
          embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ))) =
        act U2' (act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ) -
          embedVec (fun m => padTo (wires D k) (cmid D m)) φ) +
        (act U2' (embedVec (fun m => padTo (wires D k) (cmid D m)) φ) -
          embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ)))) := by
      apply WithLp.ofLp_injective
      simp only [WithLp.ofLp_add, WithLp.ofLp_sub, act, WithLp.ofLp_toLp, Matrix.mulVec_sub]
      funext z
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have herr1 : ‖act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ) -
        embedVec (fun m => padTo (wires D k) (cmid D m)) φ‖ ≤ (1 / 2 : ℝ) ^ (k + 1) * ‖ψ‖ := by
      rw [padEmbedVec_embedVec hin1 hle1 (cin D) ψ,
          padEmbedVec_embedVec hmid1 hle1 (cmid D) φ]
      change ‖act (circUnitary (mapCirc
          (shiftEmb 0 (wires1 D (k + 1)) (wires D k)
            (by dsimp only [wires]; omega)) (circ1 D (k + 1))))
          (padEmbedVec hle1 _) - _‖ ≤ _
      rw [act_circUnitary_mapCirc_shift hle1, ← padEmbedVec_sub, norm_padEmbedVec]
      exact himp1_k ψ
    have herr2 : ‖act U2' (embedVec (fun m => padTo (wires D k) (cmid D m)) φ) -
        embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ)))‖ ≤
        (1 / 2 : ℝ) ^ (k + 1) * ‖ψ‖ := by
      rw [padEmbedVec_embedVec hmid2 hle2 (cmid D) φ,
          padEmbedVec_embedVec hout2 hle2 (cout D) _]
      change ‖act (circUnitary (mapCirc
          (shiftEmb 0 (wires2 D (k + 1)) (wires D k)
            (by dsimp only [wires]; omega)) (circ2 D (k + 1))))
          (padEmbedVec hle2 _) - _‖ ≤ _
      rw [act_circUnitary_mapCirc_shift hle2, ← padEmbedVec_sub, norm_padEmbedVec]
      refine (himp2_k φ).trans ?_
      exact mul_le_mul_of_nonneg_left (hbnd D hD ψ) (by positivity)
    calc
      ‖act U2' (act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ)) -
          embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ)))‖
        ≤ ‖act U2' (act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ) -
            embedVec (fun m => padTo (wires D k) (cmid D m)) φ)‖ +
          ‖act U2' (embedVec (fun m => padTo (wires D k) (cmid D m)) φ) -
            embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ)))‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ = ‖act U1' (embedVec (fun x => padTo (wires D k) (cin D x)) ψ) -
            embedVec (fun m => padTo (wires D k) (cmid D m)) φ‖ +
          ‖act U2' (embedVec (fun m => padTo (wires D k) (cmid D m)) φ) -
            embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ2 D).mulVec (WithLp.ofLp φ)))‖ := by
          rw [act_norm_of_mem_unitaryGroup hU2']
      _ ≤ (1 / 2 : ℝ) ^ (k + 1) * ‖ψ‖ + (1 / 2 : ℝ) ^ (k + 1) * ‖ψ‖ := add_le_add herr1 herr2
      _ = (1 / 2 : ℝ) ^ k * ‖ψ‖ := by ring
