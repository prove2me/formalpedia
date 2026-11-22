-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:58:29.726643+00:00
-- url     : https://prove2.me/submissions/bd155073-7ac3-4cbf-a47e-fa9f1e2611bb

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

noncomputable section

open Classical
open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_Adjoint_Aux

open Turing Polynomial Function
open OAI.MetricKMedian.Binary

/-! ### Part 1: Finite-TM2 Composition and Output-Length Bounds -/

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

end TM2Plumbing

/-! ### Part 2: Classical PolyTime Inverter for Circuit Encoding -/

section PolyAdj

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly
open QMCNumericRuntime

def qBit (b : Bool) : List Bool := [true, true, true, b, true, false]

def parseAdj : Transducer where
  Q := Fin 10
  initial := 0
  next q b :=
    if q = 0 then (if b then (0, qBit true) else (1, qBit false ++ [false]))
    else if q = 1 then (if b then (1, []) else (2, []))
    else if q = 2 then (if b then (3, qBit true) else (7, qBit false))
    else if q = 3 then (if b then (4, qBit true) else (7, qBit false))
    else if q = 4 then (if b then (5, qBit true) else (7, qBit false))
    else if q = 5 then (if b then (6, qBit true) else (7, qBit false))
    else if q = 6 then (if b then (9, [false]) else (8, qBit false))
    else if q = 7 then (if b then (7, qBit true) else (2, qBit false ++ [false]))
    else if q = 8 then (if b then (8, qBit true) else (7, qBit false))
    else (9, [])
  finish q :=
    if q = 0 then [false]
    else if q = 1 then []
    else if q = 2 then []
    else if q = 9 then []
    else [false]

def consHead (b : Bool) : List (List Bool) → List (List Bool)
  | [] => [[b]]
  | hd :: tl => (b :: hd) :: tl

def consHeadList (pre : List Bool) : List (List Bool) → List (List Bool)
  | [] => [pre]
  | hd :: tl => (pre ++ hd) :: tl

lemma consHead_consHeadList (b : Bool) (pre : List Bool) (L : List (List Bool)) (hne : L ≠ []) :
    consHead b (consHeadList pre L) = consHeadList (b :: pre) L := by
  cases L with
  | nil => exact absurd rfl hne
  | cons hd tl => rfl

def parseInstrs : Fin 10 → List Bool → List (List Bool)
  | 2, [] => []
  | 2, true :: xs => consHead true (parseInstrs 3 xs)
  | 2, false :: xs => consHead false (parseInstrs 7 xs)
  | 3, [] => [[]]
  | 3, true :: xs => consHead true (parseInstrs 4 xs)
  | 3, false :: xs => consHead false (parseInstrs 7 xs)
  | 4, [] => [[]]
  | 4, true :: xs => consHead true (parseInstrs 5 xs)
  | 4, false :: xs => consHead false (parseInstrs 7 xs)
  | 5, [] => [[]]
  | 5, true :: xs => consHead true (parseInstrs 6 xs)
  | 5, false :: xs => consHead false (parseInstrs 7 xs)
  | 6, [] => [[]]
  | 6, true :: _ => [[]]
  | 6, false :: xs => consHead false (parseInstrs 8 xs)
  | 7, [] => [[]]
  | 7, true :: xs => consHead true (parseInstrs 7 xs)
  | 7, false :: xs => [false] :: parseInstrs 2 xs
  | 8, [] => [[]]
  | 8, true :: xs => consHead true (parseInstrs 8 xs)
  | 8, false :: xs => consHead false (parseInstrs 7 xs)
  | _, _ => []

def parseLen : List Bool → List (List Bool)
  | [] => []
  | true :: xs => parseLen xs
  | false :: xs => parseInstrs 2 xs

def parseW : List Bool → List Bool × List (List Bool)
  | [] => ([], [])
  | true :: xs => let p := parseW xs; (true :: p.1, p.2)
  | false :: xs => ([false], parseLen xs)

lemma quote_encodeList_cons (b : Bool) (xs : List Bool) :
    quote (encodeList encodeBool (b :: xs)) = qBit b ++ quote (encodeList encodeBool xs) := by
  simp [encodeList, encodeBool, quote, qBit]

lemma encList_cons (hd : List Bool) (tl : List (List Bool)) :
    encodeList (encodeList encodeBool) (hd :: tl) =
      quote (encodeList encodeBool hd) ++ encodeList (encodeList encodeBool) tl := rfl

lemma consHead_ne_nil (b : Bool) (L : List (List Bool)) : consHead b L ≠ [] := by
  cases L <;> simp [consHead]

lemma parseInstrs_ne_nil (q : Fin 10) (hq : q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8)
    (xs : List Bool) : parseInstrs q xs ≠ [] := by
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases xs with
    | nil => simp [parseInstrs]
    | cons b xs => cases b <;> simp [parseInstrs, consHead_ne_nil]

lemma run_consHead (b : Bool) (L : List (List Bool)) (hne : L ≠ []) :
    encodeList (encodeList encodeBool) (consHead b L) =
      qBit b ++ encodeList (encodeList encodeBool) L := by
  cases L with
  | nil => exact absurd rfl hne
  | cons hd tl =>
    simp only [consHead, encList_cons, quote_encodeList_cons, List.append_assoc]

lemma parseAdj_run_instrs (xs : List Bool) (q : Fin 10)
    (hq : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9) :
    parseAdj.run q xs = encodeList (encodeList encodeBool) (parseInstrs q xs) := by
  induction xs generalizing q with
  | nil =>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Transducer.run, parseAdj, parseInstrs, encodeList, quote]
  | cons b xs ih =>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · cases b
      · change qBit false ++ parseAdj.run (7 : Fin 10) xs = _
        rw [ih 7 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 7 (by simp) xs)]
      · change qBit true ++ parseAdj.run (3 : Fin 10) xs = _
        rw [ih 3 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 3 (by simp) xs)]
    · cases b
      · change qBit false ++ parseAdj.run (7 : Fin 10) xs = _
        rw [ih 7 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 7 (by simp) xs)]
      · change qBit true ++ parseAdj.run (4 : Fin 10) xs = _
        rw [ih 4 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 4 (by simp) xs)]
    · cases b
      · change qBit false ++ parseAdj.run (7 : Fin 10) xs = _
        rw [ih 7 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 7 (by simp) xs)]
      · change qBit true ++ parseAdj.run (5 : Fin 10) xs = _
        rw [ih 5 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 5 (by simp) xs)]
    · cases b
      · change qBit false ++ parseAdj.run (7 : Fin 10) xs = _
        rw [ih 7 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 7 (by simp) xs)]
      · change qBit true ++ parseAdj.run (6 : Fin 10) xs = _
        rw [ih 6 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 6 (by simp) xs)]
    · cases b
      · change qBit false ++ parseAdj.run (8 : Fin 10) xs = _
        rw [ih 8 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 8 (by simp) xs)]
      · change [false] ++ parseAdj.run (9 : Fin 10) xs = _
        have h9 : parseInstrs 9 xs = [] := by cases xs <;> rfl
        rw [ih 9 (by simp), h9]
        rfl
    · cases b
      · change (qBit false ++ [false]) ++ parseAdj.run (2 : Fin 10) xs = _
        rw [ih 2 (by simp), parseInstrs]
        simp [encodeList, encodeBool, quote, qBit]
      · change qBit true ++ parseAdj.run (7 : Fin 10) xs = _
        rw [ih 7 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 7 (by simp) xs)]
    · cases b
      · change qBit false ++ parseAdj.run (7 : Fin 10) xs = _
        rw [ih 7 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 7 (by simp) xs)]
      · change qBit true ++ parseAdj.run (8 : Fin 10) xs = _
        rw [ih 8 (by simp), parseInstrs, run_consHead _ _ (parseInstrs_ne_nil 8 (by simp) xs)]
    · cases b <;>
      · change [] ++ parseAdj.run (9 : Fin 10) xs = _
        rw [ih 9 (by simp)]
        simp [parseInstrs, encodeList]

lemma parseAdj_run_len (xs : List Bool) :
    parseAdj.run (1 : Fin 10) xs = encodeList (encodeList encodeBool) (parseLen xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b
    · change [] ++ parseAdj.run (2 : Fin 10) xs = _
      rw [parseAdj_run_instrs xs 2 (by simp)]
      rfl
    · change [] ++ parseAdj.run (1 : Fin 10) xs = _
      rw [ih]
      rfl

lemma parseAdj_run_w (xs : List Bool) :
    parseAdj.run (0 : Fin 10) xs =
      encodePair (encodeList encodeBool) (encodeList (encodeList encodeBool)) (parseW xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b
    · change (qBit false ++ [false]) ++ parseAdj.run (1 : Fin 10) xs = _
      rw [parseAdj_run_len xs]
      simp [parseW, encodePair, encodeList, encodeBool, quote, qBit]
    · change qBit true ++ parseAdj.run (0 : Fin 10) xs = _
      rw [ih]
      simp [parseW, encodePair, quote_encodeList_cons, List.append_assoc]

lemma parseLen_encNat (len : ℕ) (rest : List Bool) :
    parseLen (encNat len ++ rest) = parseInstrs 2 rest := by
  induction len with
  | zero => rfl
  | succ len ih => exact ih

lemma parseW_encNat (w : ℕ) (rest : List Bool) :
    parseW (encNat w ++ rest) = (encNat w, parseLen rest) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    change parseW (true :: (encNat w ++ rest)) = (true :: encNat w, parseLen rest)
    simp only [parseW, ih]

lemma parseInstrs_readArg1 (k : ℕ) (rest : List Bool) :
    parseInstrs 7 (encNat k ++ rest) = (encNat k) :: parseInstrs 2 rest := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change parseInstrs 7 (true :: (encNat k ++ rest)) = (true :: encNat k) :: parseInstrs 2 rest
    simp only [parseInstrs, ih, consHead]

lemma parseInstrs_readArg2 (k : ℕ) (rest : List Bool) :
    parseInstrs 8 (encNat k ++ rest) = consHeadList (encNat k) (parseInstrs 7 rest) := by
  induction k with
  | zero =>
    change parseInstrs 8 (false :: rest) = consHeadList [false] (parseInstrs 7 rest)
    simp only [parseInstrs]
    cases h7 : parseInstrs 7 rest with
    | nil => exact absurd h7 (parseInstrs_ne_nil 7 (by simp) rest)
    | cons hd tl => rfl
  | succ k ih =>
    change parseInstrs 8 (true :: (encNat k ++ rest)) =
      consHeadList (true :: encNat k) (parseInstrs 7 rest)
    rw [parseInstrs, ih, consHead_consHeadList _ _ _ (parseInstrs_ne_nil 7 (by simp) rest)]

lemma parseInstrs_instr {w : ℕ} (g : Instr w) (rest : List Bool) :
    parseInstrs 2 (encInstr g ++ rest) = encInstr g :: parseInstrs 2 rest := by
  cases g with
  | h i =>
    change parseInstrs 2 (false :: (encNat i.val ++ rest)) =
      (false :: encNat i.val) :: parseInstrs 2 rest
    simp only [parseInstrs, parseInstrs_readArg1, consHead]
  | s i =>
    change parseInstrs 2 (true :: false :: (encNat i.val ++ rest)) =
      (true :: false :: encNat i.val) :: parseInstrs 2 rest
    simp only [parseInstrs, parseInstrs_readArg1, consHead]
  | t i =>
    change parseInstrs 2 (true :: true :: false :: (encNat i.val ++ rest)) =
      (true :: true :: false :: encNat i.val) :: parseInstrs 2 rest
    simp only [parseInstrs, parseInstrs_readArg1, consHead]
  | x i =>
    change parseInstrs 2 (true :: true :: true :: false :: (encNat i.val ++ rest)) =
      (true :: true :: true :: false :: encNat i.val) :: parseInstrs 2 rest
    simp only [parseInstrs, parseInstrs_readArg1, consHead]
  | cnot i j _ =>
    change parseInstrs 2 (true :: true :: true :: true :: false ::
        ((encNat i.val ++ encNat j.val) ++ rest)) =
      (true :: true :: true :: true :: false :: (encNat i.val ++ encNat j.val)) ::
        parseInstrs 2 rest
    rw [List.append_assoc]
    simp only [parseInstrs]
    rw [parseInstrs_readArg2, parseInstrs_readArg1]
    rfl

lemma parseInstrs_circ {w : ℕ} (c : List (Instr w)) :
    parseInstrs 2 (c.map encInstr).flatten = c.map encInstr := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    simp only [List.map_cons, List.flatten_cons]
    rw [parseInstrs_instr, ih]

lemma parseW_eq {w : ℕ} (c : List (Instr w)) :
    parseW (encNat w ++ encLayer c) = (encNat w, c.map encInstr) := by
  simp only [encLayer, encStr, List.length_map]
  rw [parseW_encNat, parseLen_encNat, parseInstrs_circ]

def expandInstrStr (s : List Bool) : List (List Bool) :=
  if s[0]?.getD false then
    if !(s[1]?.getD true) then [s, s, s]
    else if !(s[2]?.getD true) then [s, s, s, s, s, s, s]
    else [s]
  else [s]

lemma expandInstrStr_encInstr {w : ℕ} (g : Instr w) :
    expandInstrStr (encInstr g) = (instrInv g).map encInstr := by
  cases g with
  | h i => simp [expandInstrStr, encInstr, encNat, instrInv]
  | s i => simp [expandInstrStr, encInstr, encNat, instrInv]
  | t i => simp [expandInstrStr, encInstr, encNat, instrInv]
  | x i => simp [expandInstrStr, encInstr, encNat, instrInv]
  | cnot i j _ => simp [expandInstrStr, encInstr, encNat, instrInv]

def adjBody (p : List Bool × List (List Bool)) : List Bool :=
  let inv := p.2.reverse.flatMap expandInstrStr
  p.1 ++ (inv.map (fun _ => true) ++ [false]) ++ inv.flatMap id

@[fun_prop] lemma expandInstrStr_poly : Poly expandInstrStr := by
  unfold expandInstrStr
  fun_prop

@[fun_prop] lemma adjBody_poly : Poly adjBody := by
  unfold adjBody
  fun_prop

lemma adjBody_eq {w : ℕ} (c : List (Instr w)) :
    adjBody (encNat w, c.map encInstr) = encNat w ++ encLayer (circInv c) := by
  unfold adjBody
  dsimp only
  have hflat : ((c.map encInstr).reverse.flatMap expandInstrStr) =
      (circInv c).map encInstr := by
    rw [← List.map_reverse, List.flatMap_map]
    simp only [circInv, List.map_flatten, List.map_map, Function.comp_def, expandInstrStr_encInstr]
    rfl
  rw [hflat]
  have hrep : (((circInv c).map encInstr).map (fun _ => true)) =
      List.replicate (circInv c).length true := by
    induction circInv c with
    | nil => rfl
    | cons _ _ ih => simp [List.replicate_succ, ih]
  have hid : ((circInv c).map encInstr).flatMap id = ((circInv c).map encInstr).flatten := by
    induction ((circInv c).map encInstr) with
    | nil => rfl
    | cons hd tl ih => simp [List.flatMap_cons, List.flatten_cons, ih]
  rw [hrep, hid]
  simp [encLayer, encStr, encNat, List.append_assoc]

noncomputable def adjProgram :
    PolyProgram id id (adjBody ∘ parseW) :=
  let p1 : PolyProgram id enc parseW :=
    parseAdj.program.recode id (fun _ => rfl) (fun xs => parseAdj_run_w xs)
  let p2 : PolyProgram enc id adjBody :=
    adjBody_poly.program.comp BooleanLists.unpackProgram
  p1.comp p2

end PolyAdj

/-! ### Part 3: Unitarity and Adjoint Identity for Clifford+T Circuits -/

section QuantumAdjoint

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

lemma phaseS_cube : phaseS * phaseS * phaseS = phaseS.conjTranspose := by
  ext a b; cases a <;> cases b <;> simp [phaseS, Matrix.mul_apply]

lemma phaseS_unitary : phaseS * phaseS.conjTranspose = 1 := by
  ext a b; cases a <;> cases b <;> simp [phaseS, Matrix.mul_apply]

lemma gateT_seven :
    gateT * gateT * gateT * gateT * gateT * gateT * gateT = gateT.conjTranspose := by
  ext a b
  cases a <;> cases b <;> simp [gateT, Matrix.mul_apply]
  rw [← Complex.exp_conj]
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  simp only [← Complex.exp_add]
  have h1 : Complex.I * ↑Real.pi / 4 + Complex.I * ↑Real.pi / 4 + Complex.I * ↑Real.pi / 4 +
      Complex.I * ↑Real.pi / 4 + Complex.I * ↑Real.pi / 4 + Complex.I * ↑Real.pi / 4 +
      Complex.I * ↑Real.pi / 4 =
      -(Complex.I * ↑Real.pi / 4) + (1 : ℤ) * (2 * ↑Real.pi * Complex.I) := by
    push_cast; ring
  rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp only [mul_one]
  congr 1; ring

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

lemma circUnitary_instrInv {n : ℕ} (g : Instr n) :
    circUnitary (instrInv g) = (circUnitary [g]).conjTranspose := by
  cases g with
  | h i =>
    simp only [instrInv, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    change embedOp (hadamard.submatrix q1Equiv q1Equiv) (wire1 i) =
      (embedOp (hadamard.submatrix q1Equiv q1Equiv) (wire1 i)).conjTranspose
    rw [← embedOp_conjTranspose, submatrix_equiv_conjTranspose, hadamard_conjTranspose]
  | s i =>
    simp only [instrInv, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]
    change embedOp (phaseS.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (phaseS.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (phaseS.submatrix q1Equiv q1Equiv) (wire1 i) =
      (embedOp (phaseS.submatrix q1Equiv q1Equiv) (wire1 i)).conjTranspose
    rw [← embedOp_conjTranspose, ← embedOp_mul, ← embedOp_mul,
      submatrix_equiv_conjTranspose, submatrix_equiv_mul, submatrix_equiv_mul, phaseS_cube]
  | t i =>
    simp only [instrInv, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one]
    change embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) *
        embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) =
      (embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i)).conjTranspose
    rw [← embedOp_conjTranspose, ← embedOp_mul, ← embedOp_mul, ← embedOp_mul, ← embedOp_mul,
      ← embedOp_mul, ← embedOp_mul, submatrix_equiv_conjTranspose,
      submatrix_equiv_mul, submatrix_equiv_mul, submatrix_equiv_mul, submatrix_equiv_mul,
      submatrix_equiv_mul, submatrix_equiv_mul, gateT_seven]
  | x i =>
    simp only [instrInv, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    change embedOp (pauliX.submatrix q1Equiv q1Equiv) (wire1 i) =
      (embedOp (pauliX.submatrix q1Equiv q1Equiv) (wire1 i)).conjTranspose
    rw [← embedOp_conjTranspose, submatrix_equiv_conjTranspose, pauliX_conjTranspose]
  | cnot i j hij =>
    simp only [instrInv, circUnitary, Circuit.unitary, List.map_cons, List.map_nil,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    change embedOp (cnot.submatrix q2Equiv q2Equiv) (wire2 i j hij) =
      (embedOp (cnot.submatrix q2Equiv q2Equiv) (wire2 i j hij)).conjTranspose
    rw [← embedOp_conjTranspose, submatrix_equiv_conjTranspose, cnot_conjTranspose]

lemma circUnitary_circInv {n : ℕ} (c : List (Instr n)) :
    circUnitary (circInv c) = (circUnitary c).conjTranspose := by
  induction c with
  | nil => simp [circInv, circUnitary, Circuit.unitary]
  | cons g c ih =>
    have hinv : circInv (g :: c) = circInv c ++ instrInv g := by
      simp [circInv, List.reverse_cons, List.map_append, List.flatten_append]
    have hcons : circUnitary (g :: c) = circUnitary c * circUnitary [g] := by
      simpa using circUnitary_append [g] c
    rw [hinv, circUnitary_append, ih, circUnitary_instrInv, hcons, Matrix.conjTranspose_mul]

lemma norm_mulVec_of_iso {X Y : Type} [Fintype X] [Fintype Y]
    (M : Matrix Y X ℂ) (hM : M.conjTranspose * M = 1) (ψ : EuclideanSpace ℂ X) :
    ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ = ‖ψ‖ := by
  have hnorm_sq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ),
      ((∑ i : ι, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i : ι, star (v i) * v i := by
    intro ι _ v
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, RCLike.star_def]
  have hlhs_c : ((‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 : ℝ) : ℂ) =
      ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [hnorm_sq, hnorm_sq]
    simp_rw [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_comm]
    have hx : ∀ x₂ : X, (∑ y : Y, star (WithLp.ofLp ψ x₁) * star (M y x₁) *
        (M y x₂ * WithLp.ofLp ψ x₂)) =
        star (WithLp.ofLp ψ x₁) * ((∑ y : Y, star (M y x₁) * M y x₂) * WithLp.ofLp ψ x₂) := by
      intro x₂
      simp only [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => by ring
    simp_rw [hx]
    have hinner : ∀ x₂ : X, (∑ y : Y, star (M y x₁) * M y x₂) = (1 : Matrix X X ℂ) x₁ x₂ := by
      intro x₂
      have := congrFun (congrFun hM x₁) x₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    simp_rw [hinner, Matrix.one_apply]
    simp
  have hsq : ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 = ‖ψ‖ ^ 2 :=
    Complex.ofReal_injective hlhs_c
  nlinarith [norm_nonneg (WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))), norm_nonneg ψ]

lemma circInv_length_le {n : ℕ} (c : List (Instr n)) :
    (circInv c).length ≤ 7 * c.length := by
  induction c with
  | nil => simp [circInv]
  | cons g c ih =>
    have hinv : circInv (g :: c) = circInv c ++ instrInv g := by
      simp [circInv, List.reverse_cons, List.map_append, List.flatten_append]
    have hlen : (instrInv g).length ≤ 7 := by cases g <;> simp [instrInv]
    rw [hinv, List.length_append, List.length_cons]
    omega

end QuantumAdjoint

end GL2QFT_Adjoint_Aux

open GL2QFT_Adjoint_Aux

theorem solution {P : FieldData → Prop} {X Y : FieldData → Type}
    [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ}
    {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)}
    {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (h : UniformlyImplementsOn P cin cout Φ)
    (hu : ∀ D, P D → (Φ D).conjTranspose * (Φ D) = 1 ∧ (Φ D) * (Φ D).conjTranspose = 1) :
    UniformlyImplementsOn P cout cin (fun D => (Φ D).conjTranspose) := by
  rcases h with ⟨wires, circ, f, c, hf_poly, hf_eq, hlen, himp⟩
  obtain ⟨mf⟩ := hf_poly
  refine ⟨wires, fun D k => circInv (circ D k), (adjBody ∘ parseW) ∘ f, 7 * c, ?_, ?_, ?_, ?_⟩
  · exact ⟨TM2Comp.comp mf adjProgram.stock⟩
  · intro D hD k
    simp only [Function.comp_apply]
    rw [hf_eq D hD k, parseW_eq, adjBody_eq]
  · intro D hD k
    have h1 := circInv_length_le (circ D k)
    have h2 := hlen D hD k
    have hpow : (Nat.log 2 D.q + k + 2) ^ c ≤ (Nat.log 2 D.q + k + 2) ^ (7 * c) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc
      (circInv (circ D k)).length ≤ 7 * (circ D k).length := h1
      _ ≤ 7 * (c * (Nat.log 2 D.q + k + 2) ^ c) := Nat.mul_le_mul_left 7 h2
      _ = (7 * c) * (Nat.log 2 D.q + k + 2) ^ c := by ring
      _ ≤ (7 * c) * (Nat.log 2 D.q + k + 2) ^ (7 * c) := Nat.mul_le_mul_left (7 * c) hpow
  · intro D hD k
    obtain ⟨hin, hout, himp_k⟩ := himp D hD k
    refine ⟨hout, hin, ?_⟩
    intro ψ
    set U := circUnitary (circ D k)
    have hU : U ∈ Matrix.unitaryGroup (Qubits (wires D k)) ℂ := circUnitary_mem_unitaryGroup _
    have hUU : U.conjTranspose * U = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hU
    have hUh : U.conjTranspose ∈ Matrix.unitaryGroup (Qubits (wires D k)) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      simpa [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff').mp hU
    let φ : EuclideanSpace ℂ (X D) :=
      WithLp.toLp 2 ((Φ D).conjTranspose.mulVec (WithLp.ofLp ψ))
    have hΦφ : WithLp.toLp 2 ((Φ D).mulVec (WithLp.ofLp φ)) = ψ := by
      apply WithLp.ofLp_injective
      simp only [φ, Matrix.mulVec_mulVec]
      rw [(hu D hD).2, Matrix.one_mulVec]
    have hnormφ : ‖φ‖ = ‖ψ‖ := by
      refine norm_mulVec_of_iso (Φ D).conjTranspose ?_ ψ
      simpa [Matrix.conjTranspose_conjTranspose] using (hu D hD).2
    have hdiff : act U.conjTranspose
        (act U (embedVec (fun x => padTo (wires D k) (cin D x)) φ) -
         embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ D).mulVec (WithLp.ofLp φ)))) =
        -(act (circUnitary (circInv (circ D k)))
          (embedVec (fun y => padTo (wires D k) (cout D y)) ψ) -
         embedVec (fun x => padTo (wires D k) (cin D x))
          (WithLp.toLp 2 ((Φ D).conjTranspose.mulVec (WithLp.ofLp ψ)))) := by
      rw [circUnitary_circInv]
      change act U.conjTranspose (act U (embedVec (fun x => padTo (wires D k) (cin D x)) φ) -
          embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ D).mulVec (WithLp.ofLp φ)))) =
        -(act U.conjTranspose (embedVec (fun y => padTo (wires D k) (cout D y)) ψ) -
          embedVec (fun x => padTo (wires D k) (cin D x)) φ)
      rw [hΦφ]
      apply WithLp.ofLp_injective
      simp only [WithLp.ofLp_sub, WithLp.ofLp_neg, act, WithLp.ofLp_toLp, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
      funext z
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    have hnorm := act_norm_of_mem_unitaryGroup hUh
      (act U (embedVec (fun x => padTo (wires D k) (cin D x)) φ) -
       embedVec (fun y => padTo (wires D k) (cout D y)) (WithLp.toLp 2 ((Φ D).mulVec (WithLp.ofLp φ))))
    rw [hdiff, norm_neg] at hnorm
    rw [hnorm, ← hnormφ]
    exact himp_k φ
