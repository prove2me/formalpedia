-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_sum
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T07:48:00.301264+00:00
-- url     : https://prove2.me/submissions/9144f41c-09fe-4cf0-ab96-64d870471066

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option autoImplicit false

noncomputable section

open Classical
open scoped BigOperators
open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_Sum_Aux

open Turing Polynomial Function
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open OAI.MetricKMedian.Binary.Automatic.Poly

/-! ### Part 1: Finite-TM2 Composition and Fanout (`TM2Comp`, `TM2Fanout`) -/

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
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_comp, id_eq] at hm hn ⊢
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
abbrev Cfg := TM2.Cfg (Γ M N) (Label M N) (State M N)
def clean (v : State M N) : State M N := (v.1, v.2.1, none)

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
    · dsimp [leftStack]
      rw [Function.update_of_ne (by simp)]
      rcases j with j | j <;> rfl
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
  induction q with
  | push k f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | peek k f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | pop k f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | load f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | branch f q r ihq ihr => simp only [DepEmbedding.stmt, ihq, ihr]; rfl
  | goto f => rfl
  | halt => rfl

lemma right_stmt_indep (m1 m2 : ∀ k, List (M.tm.Γ k)) (q : TM2.Stmt N.tm.Γ N.tm.Λ N.tm.σ) :
    (right M N m1).stmt q = (right M N m2).stmt q := by
  induction q with
  | push k f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | peek k f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | pop k f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | load f q ih => simp only [DepEmbedding.stmt, ih]; rfl
  | branch f q r ihq ihr => simp only [DepEmbedding.stmt, ihq, ihr]; rfl
  | goto f => rfl
  | halt => rfl

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
    · rcases k with ⟨v, hk⟩
      match v with
      | 0 =>
        have hk0 : (Sum.inr (Sum.inr ⟨0, hk⟩) : Key M N) = inpKey M N := rfl
        rw [hk0, Function.update_self]; rfl
      | 1 => rw [Function.update_of_ne (by simp [inpKey])]; rfl
      | 2 => rw [Function.update_of_ne (by simp [inpKey])]; rfl
      | n + 3 => omega

lemma stk_update_buf (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os bs' : List Bool) :
    Function.update (stk M N ms ns is bs os) (bufKey M N) bs' = stk M N ms ns is bs' os := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [bufKey])]; rfl
  · rcases k with k | k
    · rw [Function.update_of_ne (by simp [bufKey])]; rfl
    · rcases k with ⟨v, hk⟩
      match v with
      | 0 => rw [Function.update_of_ne (by simp [bufKey])]; rfl
      | 1 =>
        have hk1 : (Sum.inr (Sum.inr ⟨1, hk⟩) : Key M N) = bufKey M N := rfl
        rw [hk1, Function.update_self]; rfl
      | 2 => rw [Function.update_of_ne (by simp [bufKey])]; rfl
      | n + 3 => omega

lemma stk_update_out (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os os' : List Bool) :
    Function.update (stk M N ms ns is bs os) (outKey M N) os' = stk M N ms ns is bs os' := by
  funext k
  rcases k with k | k
  · rw [Function.update_of_ne (by simp [outKey])]; rfl
  · rcases k with k | k
    · rw [Function.update_of_ne (by simp [outKey])]; rfl
    · rcases k with ⟨v, hk⟩
      match v with
      | 0 => rw [Function.update_of_ne (by simp [outKey])]; rfl
      | 1 => rw [Function.update_of_ne (by simp [outKey])]; rfl
      | 2 =>
        have hk2 : (Sum.inr (Sum.inr ⟨2, hk⟩) : Key M N) = outKey M N := rfl
        rw [hk2, Function.update_self]; rfl
      | n + 3 => omega

lemma stk_update_left (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) (k : M.tm.K) (v : List (M.tm.Γ k)) :
    Function.update (stk M N ms ns is bs os) (.inl k) v =
      stk M N (Function.update ms k v) ns is bs os := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h; rw [Function.update_self]; dsimp [stk]; rw [Function.update_self]
    · rw [Function.update_of_ne (fun he => h (Sum.inl.inj he))]; dsimp [stk]; rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; rcases j with j | j
    · rfl
    · rcases j with ⟨x, hx⟩
      match x with | 0 | 1 | 2 => rfl | n + 3 => omega

lemma stk_update_right (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) (k : N.tm.K) (v : List (N.tm.Γ k)) :
    Function.update (stk M N ms ns is bs os) (.inr (.inl k)) v =
      stk M N ms (Function.update ns k v) is bs os := by
  funext j
  rcases j with j | j
  · rw [Function.update_of_ne (by simp)]; rfl
  · rcases j with j | j
    · by_cases h : j = k
      · subst h; rw [Function.update_self]; dsimp [stk]; rw [Function.update_self]
      · rw [Function.update_of_ne (fun he => h (Sum.inl.inj (Sum.inr.inj he)))]
        dsimp [stk]; rw [Function.update_of_ne h]
    · rw [Function.update_of_ne (by simp)]
      rcases j with ⟨x, hx⟩
      match x with | 0 | 1 | 2 => rfl | n + 3 => omega

def phCfg (i : Fin 6) (ms : ∀ k, List (M.tm.Γ k)) (ns : ∀ k, List (N.tm.Γ k))
    (is bs os : List Bool) : Cfg M N :=
  ⟨some (phLabel M N i), (M.tm.initialState, N.tm.initialState, none), stk M N ms ns is bs os⟩

lemma init_eq_ph0 (s : List Bool) :
    initList (tm M N) s = phCfg M N 0 (fun _ => []) (fun _ => []) s [] [] := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · dsimp only [initList, tm, stk]
    rw [dif_neg (by simp [inpKey])]
    rfl
  · rcases k with k | k
    · dsimp only [initList, tm, stk]
      rw [dif_neg (by simp [inpKey])]
      rfl
    · fin_cases k
      · dsimp only [initList, tm, stk, inpKey]
        rw [dif_pos (by rfl)]
        simp [Equiv.coe_refl]
        rfl
      · dsimp only [initList, tm, stk]
        rw [dif_neg (by simp [inpKey])]
        rfl
      · dsimp only [initList, tm, stk]
        rw [dif_neg (by simp [inpKey])]
        rfl

lemma halt_eq (s : List Bool) :
    haltList (tm M N) s = (⟨none, (M.tm.initialState, N.tm.initialState, none),
      stk M N (fun _ => []) (fun _ => []) [] [] s⟩ : Cfg M N) := by
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · dsimp only [haltList, tm, stk]
    rw [dif_neg (by simp [outKey])]
  · rcases k with k | k
    · dsimp only [haltList, tm, stk]
      rw [dif_neg (by simp [outKey])]
    · fin_cases k
      · dsimp only [haltList, tm, stk]
        rw [dif_neg (by simp [outKey])]
      · dsimp only [haltList, tm, stk]
        rw [dif_neg (by simp [outKey])]
      · dsimp only [haltList, tm, stk, outKey]
        rw [dif_pos (by rfl)]
        simp [Equiv.coe_refl]

lemma copy_cons (b : Bool) (is bs : List Bool) :
    (tm M N).step (phCfg M N 0 (fun _ => []) (fun _ => []) (b :: is) bs []) =
      some (phCfg M N 0 (fun _ => []) (fun _ => []) is (b :: bs) []) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, Option.getD,
    List.tail, clean]
  have hb : stk M N (fun _ => []) (fun _ => []) is bs [] (bufKey M N) = bs := rfl
  rw [stk_update_inp, hb, stk_update_buf]

lemma copy_nil (bs : List Bool) :
    (tm M N).step (phCfg M N 0 (fun _ => []) (fun _ => []) [] bs []) =
      some (phCfg M N 1 (fun _ => []) (fun _ => []) [] bs []) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, List.tail, clean]
  rw [stk_update_inp]

lemma copy_run (is bs : List Bool) :
    Trace (tm M N).step (is.length + 1)
      (phCfg M N 0 (fun _ => []) (fun _ => []) is bs [])
      (phCfg M N 1 (fun _ => []) (fun _ => []) [] (is.reverse ++ bs) []) := by
  induction is generalizing bs with
  | nil =>
    exact Trace.cons (copy_nil M N bs) (Trace.refl _)
  | cons b is ih =>
    have h := Trace.cons (copy_cons M N b is bs) (ih (b :: bs))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using h

lemma dist_cons (b : Bool) (bs : List Bool) (ms : ∀ k, List (M.tm.Γ k))
    (ns : ∀ k, List (N.tm.Γ k)) :
    (tm M N).step (phCfg M N 1 ms ns [] (b :: bs) []) =
      some (phCfg M N 1
        (Function.update ms M.tm.k₀ (M.inputAlphabet.symm b :: ms M.tm.k₀))
        (Function.update ns N.tm.k₀ (N.inputAlphabet.symm b :: ns N.tm.k₀)) [] bs []) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, Option.getD,
    List.tail, clean]
  rw [stk_update_buf, stk_update_left, stk_update_right]
  rfl

lemma dist_nil (ms : List (M.tm.Γ M.tm.k₀)) (ns : List (N.tm.Γ N.tm.k₀)) :
    (tm M N).step (phCfg M N 1
        (Function.update (fun _ => []) M.tm.k₀ ms)
        (Function.update (fun _ => []) N.tm.k₀ ns) [] [] []) =
      some ((left M N (Function.update (fun _ => []) N.tm.k₀ ns)).cfg (initList M.tm ms)) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, List.tail, clean]
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
    · rcases k with ⟨x, hx⟩
      match x with | 0 | 1 | 2 => simp [DepEmbedding.cfg, left, leftStack, stk] | n + 3 => omega

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
    exact Trace.cons (dist_nil M N ms ns) (Trace.refl _)
  | cons b bs ih =>
    have hstep : (tm M N).step (phCfg M N 1
        (Function.update (fun _ => []) M.tm.k₀ ms)
        (Function.update (fun _ => []) N.tm.k₀ ns) [] (b :: bs) []) =
      some (phCfg M N 1
        (Function.update (fun _ => []) M.tm.k₀ (M.inputAlphabet.symm b :: ms))
        (Function.update (fun _ => []) N.tm.k₀ (N.inputAlphabet.symm b :: ns)) [] bs []) := by
      have hc := dist_cons M N b bs (Function.update (fun _ => []) M.tm.k₀ ms)
        (Function.update (fun _ => []) N.tm.k₀ ns)
      simpa only [Function.update_idem, Function.update_self] using hc
    have h := Trace.cons hstep (ih (M.inputAlphabet.symm b :: ms) (N.inputAlphabet.symm b :: ns))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.singleton_append] using h

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
      · subst h
        dsimp [DepEmbedding.cfg, right, rightStack, haltList, phCfg, stk]
        rw [if_pos rfl, Function.update_self]
      · dsimp [DepEmbedding.cfg, right, rightStack, haltList, phCfg, stk]
        rw [dif_neg h, Function.update_of_ne h]
    · rcases k with ⟨x, hx⟩
      match x with | 0 | 1 | 2 => rfl | n + 3 => omega

lemma drain2_cons (ms : ∀ k, List (M.tm.Γ k)) (b : N.tm.Γ N.tm.k₁) (ns : List (N.tm.Γ N.tm.k₁))
    (bs : List Bool) :
    (tm M N).step (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ (b :: ns)) [] bs []) =
      some (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ ns) [] (N.outputAlphabet b :: bs) []) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk]
  rw [Function.update_self]
  dsimp [List.head?, Option.map, Option.isSome, Option.getD, List.tail, clean]
  rw [stk_update_right, stk_update_buf, Function.update_idem]
  rfl

lemma drain2_nil (ms : ∀ k, List (M.tm.Γ k)) (bs : List Bool) :
    (tm M N).step (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ []) [] bs []) =
      some (phCfg M N 3 ms (fun _ => []) [] bs []) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk]
  rw [Function.update_self]
  dsimp [List.head?, Option.map, Option.isSome, List.tail, clean]
  rw [stk_update_right, Function.update_idem]
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · by_cases h : k = N.tm.k₁
      · subst h; simp [stk, Function.update]
      · simp [stk, Function.update, h]
    · rcases k with ⟨x, hx⟩
      match x with | 0 | 1 | 2 => rfl | n + 3 => omega

lemma drain2_run (ms : ∀ k, List (M.tm.Γ k)) (ns : List (N.tm.Γ N.tm.k₁)) (bs : List Bool) :
    Trace (tm M N).step (ns.length + 1)
      (phCfg M N 2 ms (Function.update (fun _ => []) N.tm.k₁ ns) [] bs [])
      (phCfg M N 3 ms (fun _ => []) [] ((ns.map N.outputAlphabet).reverse ++ bs) []) := by
  induction ns generalizing bs with
  | nil =>
    exact Trace.cons (drain2_nil M N ms bs) (Trace.refl _)
  | cons b ns ih =>
    have h := Trace.cons (drain2_cons M N ms b ns bs) (ih (N.outputAlphabet b :: bs))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using h

lemma emit2_cons (ms : ∀ k, List (M.tm.Γ k)) (b : Bool) (bs os : List Bool) :
    (tm M N).step (phCfg M N 3 ms (fun _ => []) [] (b :: bs) os) =
      some (phCfg M N 3 ms (fun _ => []) [] bs (b :: os)) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, Option.getD,
    List.tail, clean]
  rw [stk_update_buf, stk_update_out]
  rfl

lemma emit2_nil (ms : ∀ k, List (M.tm.Γ k)) (os : List Bool) :
    (tm M N).step (phCfg M N 3 ms (fun _ => []) [] [] os) =
      some (phCfg M N 4 ms (fun _ => []) [] [] (false :: os)) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, List.tail, clean]
  rw [stk_update_buf, stk_update_out]
  rfl

lemma emit2_run (ms : ∀ k, List (M.tm.Γ k)) (bs os : List Bool) :
    Trace (tm M N).step (bs.length + 1)
      (phCfg M N 3 ms (fun _ => []) [] bs os)
      (phCfg M N 4 ms (fun _ => []) [] [] (false :: (bs.reverse ++ os))) := by
  induction bs generalizing os with
  | nil =>
    exact Trace.cons (emit2_nil M N ms os) (Trace.refl _)
  | cons b bs ih =>
    have h := Trace.cons (emit2_cons M N ms b bs os) (ih (b :: os))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append] using h

lemma drain1_cons (b : M.tm.Γ M.tm.k₁) (ms : List (M.tm.Γ M.tm.k₁)) (bs os : List Bool) :
    (tm M N).step (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ (b :: ms)) (fun _ => []) [] bs os) =
      some (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ ms) (fun _ => []) []
        (M.outputAlphabet b :: bs) os) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk]
  rw [Function.update_self]
  dsimp [List.head?, Option.map, Option.isSome, Option.getD, List.tail, clean]
  rw [stk_update_left, stk_update_buf, Function.update_idem]
  rfl

lemma drain1_nil (bs os : List Bool) :
    (tm M N).step (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ []) (fun _ => []) [] bs os) =
      some (phCfg M N 5 (fun _ => []) (fun _ => []) [] bs os) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk]
  rw [Function.update_self]
  dsimp [List.head?, Option.map, Option.isSome, List.tail, clean]
  rw [stk_update_left, Function.update_idem]
  apply dep_cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · by_cases h : k = M.tm.k₁
    · subst h; simp [stk, Function.update]
    · simp [stk, Function.update, h]
  · rcases k with k | k
    · rfl
    · rcases k with ⟨x, hx⟩
      match x with | 0 | 1 | 2 => rfl | n + 3 => omega

lemma drain1_run (ms : List (M.tm.Γ M.tm.k₁)) (bs os : List Bool) :
    Trace (tm M N).step (ms.length + 1)
      (phCfg M N 4 (Function.update (fun _ => []) M.tm.k₁ ms) (fun _ => []) [] bs os)
      (phCfg M N 5 (fun _ => []) (fun _ => []) [] ((ms.map M.outputAlphabet).reverse ++ bs) os) := by
  induction ms generalizing bs with
  | nil =>
    exact Trace.cons (drain1_nil M N bs os) (Trace.refl _)
  | cons b ms ih =>
    have h := Trace.cons (drain1_cons M N b ms bs os) (ih (M.outputAlphabet b :: bs))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.singleton_append] using h

lemma emit1_cons (b : Bool) (bs os : List Bool) :
    (tm M N).step (phCfg M N 5 (fun _ => []) (fun _ => []) [] (b :: bs) os) =
      some (phCfg M N 5 (fun _ => []) (fun _ => []) [] bs (true :: b :: os)) := by
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, Option.getD,
    List.tail, clean]
  have h0 : stk M N (fun _ => []) (fun _ => []) [] bs (b :: os) (outKey M N) = b :: os := rfl
  have h1 : stk M N (fun _ => []) (fun _ => []) [] bs os (outKey M N) = os := rfl
  rw [stk_update_buf, h1, stk_update_out, h0, stk_update_out]

lemma emit1_nil (os : List Bool) :
    (tm M N).step (phCfg M N 5 (fun _ => []) (fun _ => []) [] [] os) =
      some (haltList (tm M N) os) := by
  rw [halt_eq]
  dsimp only [phCfg]
  rw [step_eq]
  apply congrArg some
  dsimp [code, phaseStmt, TM2.stepAux, stk, List.head?, Option.isSome, List.tail, clean]
  rw [stk_update_buf]

lemma emit1_run (bs os : List Bool) :
    Trace (tm M N).step (bs.length + 1)
      (phCfg M N 5 (fun _ => []) (fun _ => []) [] bs os)
      (haltList (tm M N) ((bs.reverse.flatMap fun b => [true, b]) ++ os)) := by
  induction bs generalizing os with
  | nil =>
    exact Trace.cons (emit1_nil M N os) (Trace.refl _)
  | cons b bs ih =>
    have h := Trace.cons (emit1_cons M N b bs os) (ih (true :: b :: os))
    dsimp only [FinTM2.Cfg, FinTM2.Γ, FinTM2.Λ, FinTM2.σ, tm] at h ⊢
    simpa only [List.length_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
      using h

lemma quote_eq_flatMap (xs ys : List Bool) :
    (xs.flatMap fun b => [true, b]) ++ (false :: ys) = quote xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.flatMap_cons, quote, List.cons_append, List.nil_append, List.append_assoc]
    exact congrArg (fun l => true :: b :: l) ih

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
    have hupd_nil : ∀ {κ : Type} [DecidableEq κ] {γ : κ → Type} (k : κ),
        Function.update (fun i : κ => ([] : List (γ i))) k [] = fun _ => [] := by
      intro κ _ γ k
      ext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    have hc := copy_run M N s []
    rw [← init_eq_ph0] at hc
    simp only [List.append_nil] at hc
    have hd := dist_run M N s.reverse [] []
    simp only [List.length_reverse, List.reverse_reverse, List.append_nil, hupd_nil] at hd
    have h1 := (left M N (Function.update (fun _ => []) N.tm.k₀ (s.map N.inputAlphabet.symm))).trace
      M.tm.m (tm M N).m (fun l => left_stmt_indep M N _ _ _) tM
    rw [left_halt_eq_right_init] at h1
    have h2 := (right M N (Function.update (fun _ => []) M.tm.k₁ ((f1 s).map M.outputAlphabet.symm))).trace
      N.tm.m (tm M N).m (fun l => right_stmt_indep M N _ _ _) tN
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
    have hout : TM2OutputsInTime (tm M N) s (some (quote (f1 s) ++ f2 s))
        (Polynomial.eval s.length
          (let sb1 := X + M.time * C (tmGrowth M.tm)
           let sb2 := X + N.time * C (tmGrowth N.tm)
           2 * X + M.time + N.time + 2 * sb1 + 2 * sb2 + 8)) := by
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
      dsimp only
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
        Polynomial.eval_C, id_eq] at hm1 hm2 ⊢
      omega
    obtain ⟨⟨st, hst⟩, hle⟩ := hout
    refine ⟨⟨st, ?_⟩, hle⟩
    refine (congrArg (fun l => (flip bind (tm M N).step)^[st] (some (initList (tm M N) l))) ?_).trans
      (hst.trans (congrArg (fun l => Option.map (haltList (tm M N)) (some l)) ?_).symm)
    · exact @List.map_id Bool s
    · exact @List.map_id Bool (quote (f1 s) ++ f2 s)

end TM2Fanout

end TM2Plumbing

/-! ### Part 2: Classical Poly Combinators (`splitFun`, `sqrtNat`, `parseW`, `packPair`, `incLast`) -/

section PolyCore

@[fun_prop] theorem nat_div : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem nat_mod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem list_reverse {α : Type} [Coding α] [Inhabited α] :
    Poly (List.reverse : List α → List α) := ⟨PolyProgram.listReverse enc default⟩
@[fun_prop] theorem list_drop {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨PolyProgram.listDrop enc default⟩
@[fun_prop] theorem list_take {α : Type} [Coding α] [Inhabited α] :
    Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨PolyProgram.listTake enc default⟩
@[fun_prop] theorem word_value_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩
@[fun_prop] theorem nat_asList_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩
@[fun_prop] theorem binary_quote_poly : Poly OAI.MetricKMedian.Binary.quote :=
  ⟨(BooleanLists.unpackProgram.comp (PolyProgram.quote.comp BooleanLists.packProgram)).congr _
    (fun _ => rfl)⟩

@[fun_prop] theorem nat_div_comp {α : Type} [Coding α] {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) := Poly.comp nat_div (Poly.pair hf hg)
@[fun_prop] theorem nat_add_comp {α : Type} [Coding α] {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)
@[fun_prop] theorem nat_sub_comp {α : Type} [Coding α] {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)
@[fun_prop] theorem bool_not_comp {α : Type} [Coding α] {f : α → Bool} (hf : Poly f) :
    Poly (fun x => !(f x)) := Poly.comp Poly.bool_not hf
@[fun_prop] theorem list_drop_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {xs : α → List β} {n : α → ℕ} (hxs : Poly xs) (hn : Poly n) :
    Poly (fun x => (xs x).drop (n x)) := Poly.comp list_drop (Poly.pair hxs hn)
@[fun_prop] theorem list_take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {xs : α → List β} {n : α → ℕ} (hxs : Poly xs) (hn : Poly n) :
    Poly (fun x => (xs x).take (n x)) := Poly.comp list_take (Poly.pair hxs hn)
@[fun_prop] theorem list_reverse_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {xs : α → List β} (hxs : Poly xs) :
    Poly (fun x => (xs x).reverse) := Poly.comp list_reverse hxs

def qBit (b : Bool) : List Bool := [true, true, true, b, true, false]

def packPair : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => if b then (some false, []) else (some true, [false])
    | some false => (none, qBit b)
    | some true => (some true, [true, b, false])
  finish q := match q with
    | none => [false]
    | some false => [false]
    | some true => []

def unpackPairAux : Option Bool → List Bool → List Bool × List Bool
  | none, [] => ([], [])
  | none, true :: xs => unpackPairAux (some false) xs
  | none, false :: xs => ([], xs)
  | some false, [] => ([], [])
  | some false, b :: xs => let p := unpackPairAux none xs; (b :: p.1, p.2)
  | some true, xs => ([], xs)

lemma packPair_run_true (xs : List Bool) :
    packPair.run (some true : Option Bool) xs = encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change [true, b, false] ++ packPair.run (some true : Option Bool) xs = _
    rw [ih]
    rfl

lemma quote_encodeList_cons (b : Bool) (xs : List Bool) :
    quote (encodeList encodeBool (b :: xs)) = qBit b ++ quote (encodeList encodeBool xs) := by
  simp [encodeList, encodeBool, quote, qBit]

lemma packPair_run_aux (q : Option Bool) (hq : q = none ∨ q = some false) (xs : List Bool) :
    packPair.run q xs =
      encodePair (encodeList encodeBool) (encodeList encodeBool) (unpackPairAux q xs) := by
  induction xs generalizing q with
  | nil =>
    rcases hq with rfl | rfl <;> rfl
  | cons b xs ih =>
    rcases hq with rfl | rfl
    · cases b
      · change [false] ++ packPair.run (some true : Option Bool) xs = _
        rw [packPair_run_true]
        rfl
      · exact ih (some false) (Or.inr rfl)
    · change qBit b ++ packPair.run (none : Option Bool) xs = _
      rw [ih none (Or.inl rfl)]
      simp only [unpackPairAux, encodePair, quote_encodeList_cons, List.append_assoc]

lemma unpackPairAux_quote (xs ys : List Bool) :
    unpackPairAux none (quote xs ++ ys) = (xs, ys) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp [quote, unpackPairAux, ih]

noncomputable def packPairProgram :
    PolyProgram id enc (fun s => unpackPairAux none s) :=
  packPair.program.recode id (fun _ => rfl) (fun s => packPair_run_aux none (Or.inl rfl) s)

noncomputable def pairFstProg : PolyProgram id id (fun s => (unpackPairAux none s).1) :=
  (packPairProgram.comp (PolyProgram.fst enc enc)).comp BooleanLists.unpackProgram

noncomputable def pairSndProg : PolyProgram id id (fun s => (unpackPairAux none s).2) :=
  (packPairProgram.comp (PolyProgram.snd enc enc)).comp BooleanLists.unpackProgram

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
        simp [encodeList, encodeBool, quote, qBit, List.append_assoc]
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
      simp [parseW, encodePair, encodeList, encodeBool, quote, qBit, List.append_assoc]
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
  simp only [encLayer, encStr, List.length_map, List.append_assoc]
  rw [parseW_encNat, parseLen_encNat, parseInstrs_circ]

@[fun_prop] theorem parseW_poly : Poly parseW :=
  ⟨(BooleanLists.unpackProgram.comp (parseAdj.program.recode id (fun _ => rfl) parseAdj_run_w)).congr
    _ (fun _ => rfl)⟩

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

@[fun_prop] lemma expandInstrStr_poly : Poly expandInstrStr := by
  unfold expandInstrStr
  fun_prop

end PolyCore

lemma findIdx_not_encNat (m : ℕ) (rest : List Bool) :
    (encNat m ++ rest).findIdx (fun b => !b) = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (true :: (encNat m ++ rest)).findIdx (fun b => !b) = m + 1
    rw [List.findIdx_cons]
    simp [ih]

lemma take_encNat (m : ℕ) (rest : List Bool) :
    (encNat m ++ rest).take (m + 1) = encNat m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (true :: (encNat m ++ rest)).take (m + 2) = true :: encNat m
    simp [List.take_succ_cons, ih]

lemma drop_encNat (m : ℕ) (rest : List Bool) :
    (encNat m ++ rest).drop (m + 1) = rest := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (true :: (encNat m ++ rest)).drop (m + 2) = rest
    simp [List.drop_succ_cons, ih]

lemma encNat_length (m : ℕ) : (encNat m).length = m + 1 := by simp [encNat]

lemma take_pred_encNat (m : ℕ) :
    (encNat m).take ((encNat m).length - 1) = List.replicate m true := by
  rw [encNat_length, Nat.add_sub_cancel, encNat]
  simpa [List.length_replicate] using List.take_left (l₁ := List.replicate m true) (l₂ := [false])

lemma list_map_true {α : Type*} (xs : List α) :
    xs.map (fun _ => true) = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [List.replicate_succ, ih]

lemma list_flatMap_id {α : Type*} (xs : List (List α)) : xs.flatMap id = xs.flatten := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [List.flatMap_cons, List.flatten_cons, ih]


lemma encNat_one_add (n : ℕ) : encNat (1 + n) = true :: encNat n := by
  simp [encNat, Nat.add_comm, List.replicate_succ]

lemma encNat_zero : encNat 0 = [false] := rfl


section QuantumCtrl

/-! ### Part 6: Quantum Unitaries, `embedOp`, `liftCtrl`, and Gate Verifications -/

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
      · rcases hex with ⟨i, rfl⟩; exact hmkU_w (fun i => u (w i)) i
      · simp only [mkU, dif_neg hex]; exact hu a (fun ⟨i, hi⟩ => hex ⟨i, hi⟩)
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
    symm
    refine Finset.sum_nbij' (fun (u : Qubits n) (i : Fin k) => u (w i)) mkU ?_ ?_ ?_ ?_ ?_
    · intro u _; exact Finset.mem_univ _
    · intro v _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmkU_off v⟩
    · intro u hu; exact hmkU_id u (Finset.mem_filter.mp hu).2
    · intro v _; funext i; exact hmkU_w v i
    · intro _ _; rfl
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

lemma embedOp_embedOp {j k n : ℕ} (M : Matrix (Qubits j) (Qubits j) ℂ)
    (u : Fin j ↪ Fin k) (e : Fin k ↪ Fin n) :
    embedOp (embedOp M u) e = embedOp M (u.trans e) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  dsimp only [Matrix, Function.comp_apply]
  have hiff : ((∀ a, a ∉ Set.range e → y a = z a) ∧ (∀ b, b ∉ Set.range u → y (e b) = z (e b))) ↔
      (∀ a, a ∉ Set.range (u.trans e) → y a = z a) := by
    constructor
    · rintro ⟨h1, h2⟩ a ha
      by_cases he : a ∈ Set.range e
      · obtain ⟨b, rfl⟩ := he
        apply h2 b
        rintro ⟨i, rfl⟩
        exact ha ⟨i, rfl⟩
      · exact h1 a he
    · intro h3
      refine ⟨fun a ha => h3 a ?_, fun b hb => h3 (e b) ?_⟩
      · rintro ⟨i, rfl⟩; exact ha ⟨u i, rfl⟩
      · rintro ⟨i, hi⟩; exact hb ⟨i, e.injective hi⟩
  by_cases h1 : ∀ a, a ∉ Set.range e → y a = z a
  · by_cases h2 : ∀ b, b ∉ Set.range u → y (e b) = z (e b)
    · have h3 := hiff.mp ⟨h1, h2⟩
      rw [if_pos h1, if_pos h2, if_pos h3]
      rfl
    · have h3 : ¬ (∀ a, a ∉ Set.range (u.trans e) → y a = z a) := fun h => h2 (hiff.mpr h).2
      rw [if_pos h1, if_neg h2, if_neg h3]
  · have h3 : ¬ (∀ a, a ∉ Set.range (u.trans e) → y a = z a) := fun h => h1 (hiff.mpr h).1
    rw [if_neg h1, if_neg h3]

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

lemma embedOp1_apply {n : ℕ} (M : Matrix Bool Bool ℂ) (i : Fin n) (z y : Qubits n) :
    embedOp (M.submatrix q1Equiv q1Equiv) (wire1 i) z y =
      if ∀ a : Fin n, a ∉ Set.range (wire1 i) → z a = y a then M (z i) (y i) else 0 := rfl

lemma embedOp2_apply {n : ℕ} (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) (i j : Fin n) (hij : i ≠ j)
    (z y : Qubits n) :
    embedOp (M.submatrix q2Equiv q2Equiv) (wire2 i j hij) z y =
      if ∀ a : Fin n, a ∉ Set.range (wire2 i j hij) → z a = y a then
        M (z i, z j) (y i, y j) else 0 := rfl

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
  simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, ← Complex.exp_add]
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
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero
  simp [map_div₀, map_mul, map_ofNat]; ring

lemma cnot_conjTranspose : cnot.conjTranspose = cnot := by
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> simp [cnot]

lemma cnot_mul_self : cnot * cnot = 1 := by
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;>
    simp [cnot, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool]

lemma submatrix1_unitary {M : Matrix Bool Bool ℂ} (hM : M * M.conjTranspose = 1) :
    (Gate.ofMatrix1 M).mat * (Gate.ofMatrix1 M).mat.conjTranspose = 1 := by
  change M.submatrix q1Equiv q1Equiv * (M.submatrix q1Equiv q1Equiv).conjTranspose = 1
  rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, hM, submatrix_equiv_one]

lemma submatrix2_unitary {M : Matrix (Bool × Bool) (Bool × Bool) ℂ} (hM : M * M.conjTranspose = 1) :
    (Gate.ofMatrix2 M).mat * (Gate.ofMatrix2 M).mat.conjTranspose = 1 := by
  change M.submatrix q2Equiv q2Equiv * (M.submatrix q2Equiv q2Equiv).conjTranspose = 1
  rw [submatrix_equiv_conjTranspose, submatrix_equiv_mul, hM, submatrix_equiv_one]

lemma instr_mem_unitaryGroup {n : ℕ} (g : Instr n) :
    embedOp (instrApp g).gate.mat (instrApp g).wires ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  apply embedOp_mem_unitaryGroup
  rw [Matrix.mem_unitaryGroup_iff]
  change (instrApp g).gate.mat * (instrApp g).gate.mat.conjTranspose = 1
  cases g with
  | h i => exact submatrix1_unitary (by rw [hadamard_conjTranspose, hadamard_mul_self])
  | s i => exact submatrix1_unitary phaseS_unitary
  | t i => exact submatrix1_unitary gateT_unitary
  | x i => exact submatrix1_unitary (by rw [pauliX_conjTranspose, pauliX_mul_self])
  | cnot i j hij => exact submatrix2_unitary (by rw [cnot_conjTranspose, cnot_mul_self])

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

lemma circUnitary_cons {n : ℕ} (g : Instr n) (c : List (Instr n)) :
    circUnitary (g :: c) = circUnitary c * circUnitary [g] := by
  simpa using circUnitary_append [g] c

lemma circUnitary_h {n : ℕ} (i : Fin n) :
    circUnitary [.h i] = embedOp (hadamard.submatrix q1Equiv q1Equiv) (wire1 i) := by
  simp only [circUnitary, Circuit.unitary, instrApp, Gate.ofMatrix1, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

lemma circUnitary_s {n : ℕ} (i : Fin n) :
    circUnitary [.s i] = embedOp (phaseS.submatrix q1Equiv q1Equiv) (wire1 i) := by
  simp only [circUnitary, Circuit.unitary, instrApp, Gate.ofMatrix1, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

lemma circUnitary_t {n : ℕ} (i : Fin n) :
    circUnitary [.t i] = embedOp (gateT.submatrix q1Equiv q1Equiv) (wire1 i) := by
  simp only [circUnitary, Circuit.unitary, instrApp, Gate.ofMatrix1, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

lemma circUnitary_x {n : ℕ} (i : Fin n) :
    circUnitary [.x i] = embedOp (pauliX.submatrix q1Equiv q1Equiv) (wire1 i) := by
  simp only [circUnitary, Circuit.unitary, instrApp, Gate.ofMatrix1, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

lemma circUnitary_cnot {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    circUnitary [.cnot i j hij] = embedOp (cnot.submatrix q2Equiv q2Equiv) (wire2 i j hij) := by
  simp only [circUnitary, Circuit.unitary, instrApp, Gate.ofMatrix2, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

lemma circUnitary_instrInv {n : ℕ} (g : Instr n) :
    circUnitary (instrInv g) = (circUnitary [g]).conjTranspose := by
  cases g with
  | h i =>
    change circUnitary [.h i] = _
    rw [circUnitary_h, ← embedOp_conjTranspose, submatrix_equiv_conjTranspose, hadamard_conjTranspose]
  | s i =>
    change circUnitary [.s i, .s i, .s i] = _
    rw [circUnitary_cons, circUnitary_cons, show circUnitary ([.s i] : List (Instr n)) = _ from circUnitary_s i]
    rw [← embedOp_mul, ← embedOp_mul, ← embedOp_conjTranspose, submatrix_equiv_mul,
      submatrix_equiv_mul, submatrix_equiv_conjTranspose, phaseS_cube]
  | t i =>
    change circUnitary [.t i, .t i, .t i, .t i, .t i, .t i, .t i] = _
    rw [circUnitary_cons, circUnitary_cons, circUnitary_cons, circUnitary_cons, circUnitary_cons,
      circUnitary_cons, show circUnitary ([.t i] : List (Instr n)) = _ from circUnitary_t i]
    rw [← embedOp_mul, ← embedOp_mul, ← embedOp_mul, ← embedOp_mul, ← embedOp_mul, ← embedOp_mul,
      ← embedOp_conjTranspose, submatrix_equiv_mul, submatrix_equiv_mul, submatrix_equiv_mul,
      submatrix_equiv_mul, submatrix_equiv_mul, submatrix_equiv_mul, submatrix_equiv_conjTranspose,
      gateT_seven]
  | x i =>
    change circUnitary [.x i] = _
    rw [circUnitary_x, ← embedOp_conjTranspose, submatrix_equiv_conjTranspose, pauliX_conjTranspose]
  | cnot i j hij =>
    change circUnitary [.cnot i j hij] = _
    rw [circUnitary_cnot, ← embedOp_conjTranspose, submatrix_equiv_conjTranspose, cnot_conjTranspose]

lemma circUnitary_circInv {n : ℕ} (c : List (Instr n)) :
    circUnitary (circInv c) = (circUnitary c).conjTranspose := by
  induction c with
  | nil => simp [circInv, circUnitary, Circuit.unitary]
  | cons g c ih =>
    have hinv : circInv (g :: c) = circInv c ++ instrInv g := by
      simp only [circInv, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [hinv, circUnitary_append, ih, circUnitary_instrInv, circUnitary_cons g c, Matrix.conjTranspose_mul]

lemma instrApp_mapInstr {m n : ℕ} (e : Fin m ↪ Fin n) (ins : Instr m) :
    circUnitary [mapInstr e ins] = embedOp (circUnitary [ins]) e := by
  cases ins with
  | h i =>
    change circUnitary [.h (e i)] = embedOp (circUnitary [.h i]) e
    rw [circUnitary_h, circUnitary_h, embedOp_embedOp]
    rfl
  | s i =>
    change circUnitary [.s (e i)] = embedOp (circUnitary [.s i]) e
    rw [circUnitary_s, circUnitary_s, embedOp_embedOp]
    rfl
  | t i =>
    change circUnitary [.t (e i)] = embedOp (circUnitary [.t i]) e
    rw [circUnitary_t, circUnitary_t, embedOp_embedOp]
    rfl
  | x i =>
    change circUnitary [.x (e i)] = embedOp (circUnitary [.x i]) e
    rw [circUnitary_x, circUnitary_x, embedOp_embedOp]
    rfl
  | cnot i j hij =>
    change circUnitary [.cnot (e i) (e j) (fun h => hij (e.injective h))] =
      embedOp (circUnitary [.cnot i j hij]) e
    rw [circUnitary_cnot, circUnitary_cnot, embedOp_embedOp]
    congr 1
    ext a
    rcases a with ⟨k, hk⟩
    match k with | 0 => rfl | 1 => rfl | n + 2 => omega

lemma circUnitary_mapCirc {m n : ℕ} (e : Fin m ↪ Fin n) (c : List (Instr m)) :
    circUnitary (mapCirc e c) = embedOp (circUnitary c) e := by
  induction c with
  | nil => simp [mapCirc, circUnitary, Circuit.unitary, embedOp_one]
  | cons g c ih =>
    have hm : mapCirc e (g :: c) = mapInstr e g :: mapCirc e c := rfl
    rw [hm, circUnitary_cons (mapInstr e g) (mapCirc e c), ih, circUnitary_cons g c, embedOp_mul,
      instrApp_mapInstr]

lemma act_mul {ι : Type} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  apply WithLp.ofLp_injective
  simp [act, Matrix.mulVec_mulVec]

lemma act_one' {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) v = v := by
  apply WithLp.ofLp_injective
  simp [act]

lemma act_add {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    act A (u + v) = act A u + act A v := by
  apply WithLp.ofLp_injective
  simp [act, Matrix.mulVec_add]

lemma act_smul {ι : Type} [Fintype ι] (A : Matrix ι ι ℂ) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    act A (c • v) = c • act A v := by
  apply WithLp.ofLp_injective
  simp [act, Matrix.mulVec_smul]

lemma act_circ_nil {n : ℕ} (v : EuclideanSpace ℂ (Qubits n)) :
    act (circUnitary ([] : List (Instr n))) v = v := by
  simp [circUnitary, Circuit.unitary, act]

lemma act_circ_cons {n : ℕ} (g₁ g₂ : Instr n) (c : List (Instr n)) (v : EuclideanSpace ℂ (Qubits n)) :
    act (circUnitary (g₁ :: g₂ :: c)) v = act (circUnitary (g₂ :: c)) (act (circUnitary [g₁]) v) := by
  rw [circUnitary_cons, act_mul]

lemma matrix_eq_of_act_ket {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (h : ∀ y : ι, act A (ket y) = act B (ket y)) : A = B := by
  ext i j
  have h1 := congrFun (congrArg WithLp.ofLp (h j)) i
  simpa [act, ket, Matrix.mulVec, dotProduct, Pi.single_apply] using h1

lemma act_embedOp1_ket {n : ℕ} (M : Matrix Bool Bool ℂ) (i : Fin n) (y : Qubits n) :
    act (embedOp (M.submatrix q1Equiv q1Equiv) (wire1 i)) (ket y) =
      M false (y i) • ket (Function.update y i false) +
      M true (y i) • ket (Function.update y i true) := by
  apply WithLp.ofLp_injective
  funext z
  simp only [act, ket, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  change (∑ x : Qubits n, embedOp (M.submatrix q1Equiv q1Equiv) (wire1 i) z x *
      (if x = y then (1 : ℂ) else 0)) = _
  rw [Finset.sum_eq_single y]
  · simp only [↓reduceIte, mul_one, embedOp1_apply]
    by_cases hzi : ∀ a : Fin n, a ∉ Set.range (wire1 i) → z a = y a
    · rw [if_pos hzi]
      have hz_eq : ∀ b : Bool, z = Function.update y i b ↔ z i = b := by
        intro b
        constructor
        · intro h; rw [h, Function.update_self]
        · intro h
          funext a
          by_cases ha : a = i
          · subst ha; simp [h]
          · rw [Function.update_of_ne ha]
            exact hzi a (fun ⟨_, hk⟩ => ha hk.symm)
      cases hzi0 : z i <;> simp [hz_eq, hzi0]
    · rw [if_neg hzi]
      have hne : ∀ b : Bool, z ≠ Function.update y i b := by
        intro b h
        apply hzi
        intro a ha
        have hai : a ≠ i := fun heq => ha ⟨0, heq.symm⟩
        rw [h, Function.update_of_ne hai]
      simp [hne]
  · intro x _ hx; simp [hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma act_h_ket {n : ℕ} (i : Fin n) (y : Qubits n) :
    act (circUnitary [.h i]) (ket y) =
      ((Real.sqrt 2 : ℂ)⁻¹) • ket (Function.update y i false) +
      (if y i then -((Real.sqrt 2 : ℂ)⁻¹) else (Real.sqrt 2 : ℂ)⁻¹) •
        ket (Function.update y i true) := by
  rw [circUnitary_h, act_embedOp1_ket]
  cases y i <;> simp [hadamard]

lemma act_s_ket {n : ℕ} (i : Fin n) (y : Qubits n) :
    act (circUnitary [.s i]) (ket y) = (if y i then Complex.I else 1) • ket y := by
  rw [circUnitary_s, act_embedOp1_ket]
  cases hy : y i
  · simp [phaseS, hy]; rw [← hy, Function.update_eq_self]
  · simp [phaseS, hy]; rw [← hy, Function.update_eq_self]

lemma act_t_ket {n : ℕ} (i : Fin n) (y : Qubits n) :
    act (circUnitary [.t i]) (ket y) =
      (if y i then Complex.exp (Complex.I * Real.pi / 4) else 1) • ket y := by
  rw [circUnitary_t, act_embedOp1_ket]
  cases hy : y i
  · simp [gateT, hy]; rw [← hy, Function.update_eq_self]
  · simp [gateT, hy]; rw [← hy, Function.update_eq_self]

lemma act_x_ket {n : ℕ} (i : Fin n) (y : Qubits n) :
    act (circUnitary [.x i]) (ket y) = ket (Function.update y i !(y i)) := by
  rw [circUnitary_x, act_embedOp1_ket]
  cases hy : y i <;> simp [pauliX]

lemma act_cnot_ket {n : ℕ} (i j : Fin n) (hij : i ≠ j) (y : Qubits n) :
    act (circUnitary [.cnot i j hij]) (ket y) = ket (Function.update y j (xor (y j) (y i))) := by
  rw [circUnitary_cnot]
  apply WithLp.ofLp_injective
  funext z
  simp only [act, ket, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, PiLp.single_apply]
  change (∑ x : Qubits n, embedOp (cnot.submatrix q2Equiv q2Equiv) (wire2 i j hij) z x *
      (if x = y then (1 : ℂ) else 0)) =
    if z = Function.update y j (xor (y j) (y i)) then (1 : ℂ) else 0
  rw [Finset.sum_eq_single y]
  · simp only [↓reduceIte, mul_one, embedOp, Matrix.of_apply, Matrix.submatrix_apply,
      q2Equiv, Equiv.coe_fn_mk, Function.comp_apply, cnot]
    have hw0 : (wire2 i j hij) 0 = i := rfl
    have hw1 : (wire2 i j hij) 1 = j := rfl
    rw [hw0, hw1]
    have hiff : ((∀ a : Fin n, a ∉ Set.range (wire2 i j hij) → z a = y a) ∧
        (z i = y i ∧ z j = xor (y j) (y i))) ↔
        z = Function.update y j (xor (y j) (y i)) := by
      constructor
      · rintro ⟨h1, h2, h3⟩
        funext a
        by_cases haj : a = j
        · subst haj; simp [h3]
        · rw [Function.update_of_ne haj]
          by_cases hai : a = i
          · subst hai; exact h2
          · apply h1 a
            rintro ⟨b, hb⟩
            rcases b with ⟨k, hk⟩
            match k with
            | 0 => exact hai hb.symm
            | 1 => exact haj hb.symm
            | n + 2 => omega
      · intro h; subst h
        refine ⟨fun a ha => ?_, ?_, Function.update_self _ _ _⟩
        · have haj : a ≠ j := fun heq => ha ⟨1, heq.symm⟩
          rw [Function.update_of_ne haj]
        · exact Function.update_of_ne hij _ y
    by_cases hz : z = Function.update y j (xor (y j) (y i))
    · obtain ⟨h1, h2, h3⟩ := hiff.mpr hz
      rw [if_pos h1, if_pos ⟨h2, h3⟩, if_pos hz]
    · have hneg : ¬ ((∀ a : Fin n, a ∉ Set.range (wire2 i j hij) → z a = y a) ∧
          (z i = y i ∧ z j = xor (y j) (y i))) := fun h => hz (hiff.mp h)
      rw [if_neg hz]
      split_ifs with h1 h23
      · exact absurd ⟨h1, h23⟩ hneg
      · rfl
      · rfl
  · intro x _ hx; simp [hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

def splitCtrl (w : ℕ) : Qubits (1 + w) ≃ Bool × Qubits w where
  toFun z := (z 0, fun j => z (Fin.natAdd 1 j))
  invFun p := Fin.append (fun _ => p.1) p.2
  left_inv z := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · have ha : a = 0 := Subsingleton.elim a 0
      subst ha; rfl
    · simp
  right_inv p := by
    rcases p with ⟨b, v⟩
    ext
    · change Fin.append (fun _ : Fin 1 => b) v (Fin.castAdd w (0 : Fin 1)) = b
      exact Fin.append_left _ _ _
    · simp

def liftCtrl (w : ℕ) (U : Matrix (Qubits w) (Qubits w) ℂ) :
    Matrix (Qubits (1 + w)) (Qubits (1 + w)) ℂ :=
  (controlled U).submatrix (splitCtrl w) (splitCtrl w)

lemma liftCtrl_one (w : ℕ) : liftCtrl w 1 = 1 := by
  ext y z
  simp only [liftCtrl, Matrix.submatrix_apply, controlled, Matrix.of_apply, Matrix.one_apply,
    splitCtrl, Equiv.coe_fn_mk]
  by_cases hyz : y = z
  · subst hyz; cases y 0 <;> simp
  · have hsp : y 0 ≠ z 0 ∨ (fun j => y (Fin.natAdd 1 j)) ≠ (fun j => z (Fin.natAdd 1 j)) := by
      by_contra! h
      exact hyz ((splitCtrl w).injective (Prod.ext h.1 h.2))
    rcases hsp with h0 | h2
    · simp [h0, hyz]
    · by_cases h0 : y 0 = z 0
      · cases hy0 : y 0 <;> simp [h0, hy0, h2, hyz]
      · simp [h0, hyz]

lemma controlled_mul {κ : Type*} [Fintype κ] [DecidableEq κ] (A B : Matrix κ κ ℂ) :
    controlled (A * B) = controlled A * controlled B := by
  ext p q
  rcases p with ⟨a, y⟩; rcases q with ⟨b, z⟩
  simp only [controlled, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    rw [Finset.sum_eq_single a]
    · cases a
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_one]
        rw [Finset.sum_eq_single y]
        · simp [Matrix.one_apply]
        · intro x _ hx; simp [Matrix.one_apply, hx.symm]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · simp [Matrix.mul_apply]
    · intro c _ hc; simp [hc.symm]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg hab]
    symm
    refine Finset.sum_eq_zero fun c _ => ?_
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hca : a = c
    · subst hca; simp [hab]
    · simp [hca]

lemma liftCtrl_mul (w : ℕ) (A B : Matrix (Qubits w) (Qubits w) ℂ) :
    liftCtrl w (A * B) = liftCtrl w A * liftCtrl w B := by
  simp only [liftCtrl, controlled_mul, submatrix_equiv_mul]

lemma liftCtrl_mem_unitaryGroup {w : ℕ} {U : Matrix (Qubits w) (Qubits w) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Qubits w) ℂ) :
    liftCtrl w U ∈ Matrix.unitaryGroup (Qubits (1 + w)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  change liftCtrl w U * (liftCtrl w U).conjTranspose = 1
  have hct : (liftCtrl w U).conjTranspose = liftCtrl w U.conjTranspose := by
    ext y z
    simp only [Matrix.conjTranspose_apply, liftCtrl, Matrix.submatrix_apply, controlled,
      Matrix.of_apply, splitCtrl, Equiv.coe_fn_mk]
    by_cases h0 : y 0 = z 0
    · cases hz0 : z 0
      · have hy0 : y 0 = false := by rw [h0, hz0]
        simp [h0, hz0, hy0, Matrix.one_apply, eq_comm]
      · have hy0 : y 0 = true := by rw [h0, hz0]
        simp [h0, hz0, hy0]
    · simp [h0, Ne.symm h0]
  rw [hct, ← liftCtrl_mul]
  change U * U.conjTranspose = 1 at hU
  rw [hU, liftCtrl_one]

lemma liftCtrl_apply {w : ℕ} (U : Matrix (Qubits w) (Qubits w) ℂ) (y z : Qubits (1 + w)) :
    liftCtrl w U y z =
      if y 0 = z 0 then
        if y 0 then U (fun j => y (Fin.natAdd 1 j)) (fun j => z (Fin.natAdd 1 j))
        else (if (fun j => y (Fin.natAdd 1 j)) = (fun j => z (Fin.natAdd 1 j)) then 1 else 0)
      else 0 := by
  simp only [liftCtrl, Matrix.submatrix_apply, splitCtrl, Equiv.coe_fn_mk, controlled, Matrix.of_apply,
    Matrix.one_apply]

lemma liftCtrl_embedOp1 {w : ℕ} (M : Matrix Bool Bool ℂ) (i : Fin w) :
    liftCtrl w (embedOp (M.submatrix q1Equiv q1Equiv) (wire1 i)) =
      embedOp ((controlled M).submatrix q2Equiv q2Equiv)
        (wire2 0 ⟨1 + i.val, by omega⟩ (by simp [Fin.ext_iff]; omega)) := by
  let t : Fin (1 + w) := ⟨1 + i.val, by omega⟩
  have h0t : (0 : Fin (1 + w)) ≠ t := by simp [t, Fin.ext_iff]; omega
  have ht : t = Fin.natAdd 1 i := Fin.ext rfl
  ext y z
  rw [liftCtrl_apply, embedOp1_apply, embedOp2_apply]
  have hw2_0 : (wire2 0 t h0t) 0 = 0 := rfl
  have hw2_1 : (wire2 0 t h0t) 1 = t := rfl
  have hiff : (∀ b : Fin w, b ∉ Set.range (wire1 i) → y (Fin.natAdd 1 b) = z (Fin.natAdd 1 b)) ↔
      (∀ a : Fin (1 + w), a ∉ Set.range (wire2 0 t h0t) → y a = z a) := by
    constructor
    · intro hb a ha
      by_cases ha0 : a.val = 0
      · have haz : a = 0 := Fin.ext ha0
        subst haz
        exact absurd ⟨0, hw2_0⟩ ha
      · let b : Fin w := ⟨a.val - 1, by omega⟩
        have hab : a = Fin.natAdd 1 b := Fin.ext (by simp [b, Fin.val_natAdd]; omega)
        rw [hab]
        apply hb b
        rintro ⟨k, hk⟩
        apply ha
        refine ⟨1, Fin.ext ?_⟩
        have hkw : (wire1 i) k = i := rfl
        rw [hkw] at hk
        rw [hw2_1, hab]
        simp [t, Fin.val_natAdd, hk]
    · intro ha b hb
      apply ha (Fin.natAdd 1 b)
      rintro ⟨k, hk⟩
      fin_cases k
      · change (wire2 0 t h0t) 0 = Fin.natAdd 1 b at hk
        rw [hw2_0] at hk
        have hv := congrArg Fin.val hk; simp [Fin.val_natAdd] at hv; omega
      · refine hb ⟨0, Fin.ext ?_⟩
        change (wire2 0 t h0t) 1 = Fin.natAdd 1 b at hk
        rw [hw2_1] at hk
        have hv := congrArg Fin.val hk
        dsimp [t] at hv; simp [Fin.val_natAdd] at hv
        have hkw : (wire1 i) 0 = i := rfl
        rw [hkw]; omega
  have hc_apply : controlled M (y 0, y t) (z 0, z t) =
      if y 0 = z 0 then if y 0 then M (y t) (z t) else if y t = z t then 1 else 0 else 0 := by
    cases hy0 : y 0 <;> cases hz0 : z 0 <;> simp [controlled, Matrix.one_apply, hy0, hz0]
  rw [hc_apply]
  by_cases h0 : y 0 = z 0
  · rw [if_pos h0]
    by_cases hc : ∀ a : Fin (1 + w), a ∉ Set.range (wire2 0 t h0t) → y a = z a
    · have hb := hiff.mpr hc
      rw [if_pos hc]
      cases hy0 : y 0
      · have hz0 : z 0 = false := by rw [← h0, hy0]
        simp only [hz0, Bool.false_eq_true, ↓reduceIte, ht]
        by_cases hyt : y (Fin.natAdd 1 i) = z (Fin.natAdd 1 i)
        · have heq : (fun j => y (Fin.natAdd 1 j)) = (fun j => z (Fin.natAdd 1 j)) :=
            _root_.funext fun b =>
              if hbi : b = i then hbi ▸ hyt else hb b (fun ⟨_, hk⟩ => hbi hk.symm)
          rw [if_pos hyt, if_pos heq]
        · rw [if_neg hyt, if_neg (fun heq => hyt (congrFun heq i))]
      · have hz0 : z 0 = true := by rw [← h0, hy0]
        simp only [↓reduceIte, ht, hz0]
        rw [if_pos hb]
    · have hnb : ¬ (∀ b : Fin w, b ∉ Set.range (wire1 i) → y (Fin.natAdd 1 b) = z (Fin.natAdd 1 b)) :=
        fun hb => hc (hiff.mp hb)
      rw [if_neg hc]
      cases hy0 : y 0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_neg (fun heq => hnb fun b _ => congrFun heq b)]
      · simp only [↓reduceIte]
        rw [if_neg hnb]
  · rw [if_neg h0]
    split_ifs <;> rfl

lemma liftCtrl_embedOp2_cnot {w : ℕ} (i j : Fin w) (hij : i ≠ j) :
    liftCtrl w (embedOp (cnot.submatrix q2Equiv q2Equiv) (wire2 i j hij)) =
      embedOp (Matrix.of fun y z : Qubits 3 =>
        if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then (1 : ℂ) else 0)
        ⟨![0, ⟨1 + i.val, by omega⟩, ⟨1 + j.val, by omega⟩], by
          intro a b hab
          fin_cases a <;> fin_cases b <;>
            dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hab
          · rfl
          · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
          · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
          · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
          · rfl
          · exact absurd (Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)) hij
          · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
          · exact absurd (Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)) hij.symm
          · rfl⟩ := by
  let e3 : Fin 3 ↪ Fin (1 + w) :=
    ⟨![0, ⟨1 + i.val, by omega⟩, ⟨1 + j.val, by omega⟩], by
      intro a b hab
      fin_cases a <;> fin_cases b <;>
        dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hab
      · rfl
      · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
      · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
      · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
      · rfl
      · exact absurd (Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)) hij
      · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
      · exact absurd (Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)) hij.symm
      · rfl⟩
  change liftCtrl w (embedOp (cnot.submatrix q2Equiv q2Equiv) (wire2 i j hij)) = embedOp _ e3
  ext y z
  rw [liftCtrl_apply, embedOp2_apply]
  have he3_apply : embedOp (Matrix.of fun u v : Qubits 3 =>
      if u 0 = v 0 ∧ u 1 = v 1 ∧ u 2 = xor (v 2) (v 0 && v 1) then (1 : ℂ) else 0) e3 y z =
      if ∀ a : Fin (1 + w), a ∉ Set.range e3 → y a = z a then
        if y 0 = z 0 ∧ y (Fin.natAdd 1 i) = z (Fin.natAdd 1 i) ∧
            y (Fin.natAdd 1 j) = xor (z (Fin.natAdd 1 j)) (z (Fin.natAdd 1 i) && z 0) then 1 else 0
      else 0 := by
    have h0 : e3 0 = 0 := rfl
    have h1 : e3 1 = Fin.natAdd 1 i := Fin.ext rfl
    have h2 : e3 2 = Fin.natAdd 1 j := Fin.ext rfl
    simp only [embedOp, Matrix.of_apply, Function.comp_apply, h0, h1, h2,
      Bool.and_comm (z 0) (z (Fin.natAdd 1 i))]
  rw [he3_apply]
  have he3_0 : e3 0 = 0 := rfl
  have he3_1 : e3 1 = Fin.natAdd 1 i := Fin.ext rfl
  have he3_2 : e3 2 = Fin.natAdd 1 j := Fin.ext rfl
  have hcnot_apply : cnot (y (Fin.natAdd 1 i), y (Fin.natAdd 1 j)) (z (Fin.natAdd 1 i), z (Fin.natAdd 1 j)) =
      if y (Fin.natAdd 1 i) = z (Fin.natAdd 1 i) ∧
          y (Fin.natAdd 1 j) = xor (z (Fin.natAdd 1 j)) (z (Fin.natAdd 1 i)) then 1 else 0 := by
    simp only [cnot, Matrix.of_apply]
  have hiff : (∀ b : Fin w, b ∉ Set.range (wire2 i j hij) → y (Fin.natAdd 1 b) = z (Fin.natAdd 1 b)) ↔
      (∀ a : Fin (1 + w), a ∉ Set.range e3 → y a = z a) := by
    constructor
    · intro hb a ha
      by_cases ha0 : a.val = 0
      · have haz : a = 0 := Fin.ext ha0
        subst haz
        exact absurd ⟨0, he3_0⟩ ha
      · let b : Fin w := ⟨a.val - 1, by omega⟩
        have hab : a = Fin.natAdd 1 b := Fin.ext (by simp [b, Fin.val_natAdd]; omega)
        rw [hab]
        apply hb b
        rintro ⟨k, hk⟩
        apply ha
        fin_cases k
        · refine ⟨1, Fin.ext ?_⟩
          have hkw : (wire2 i j hij) ((fun i : Fin 2 => i) ⟨0, by decide⟩) = i := rfl
          rw [hkw] at hk
          rw [he3_1, hk]
          simp [Fin.val_natAdd, b]; omega
        · refine ⟨2, Fin.ext ?_⟩
          have hkw : (wire2 i j hij) ((fun i : Fin 2 => i) ⟨1, by decide⟩) = j := rfl
          rw [hkw] at hk
          rw [he3_2, hk]
          simp [Fin.val_natAdd, b]; omega
    · intro ha b hb
      apply ha (Fin.natAdd 1 b)
      rintro ⟨k, hk⟩
      fin_cases k
      · change e3 0 = Fin.natAdd 1 b at hk
        rw [he3_0] at hk
        have hv := congrArg Fin.val hk; simp [Fin.val_natAdd] at hv; omega
      · refine hb ⟨0, Fin.ext ?_⟩
        change e3 1 = Fin.natAdd 1 b at hk
        rw [he3_1] at hk
        have hv := congrArg Fin.val hk; simp [Fin.val_natAdd] at hv
        have hkw : (wire2 i j hij) 0 = i := rfl
        rw [hkw]; exact hv
      · refine hb ⟨1, Fin.ext ?_⟩
        change e3 2 = Fin.natAdd 1 b at hk
        rw [he3_2] at hk
        have hv := congrArg Fin.val hk; simp [Fin.val_natAdd] at hv
        have hkw : (wire2 i j hij) 1 = j := rfl
        rw [hkw]; exact hv
  by_cases h0 : y 0 = z 0
  · rw [if_pos h0]
    by_cases hc : ∀ a : Fin (1 + w), a ∉ Set.range e3 → y a = z a
    · have hb := hiff.mpr hc
      rw [if_pos hc]
      cases hy0 : y 0
      · have hz0 : z 0 = false := by rw [← h0, hy0]
        simp only [hz0, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.xor_false,
          Matrix.one_apply, h0, eq_self_iff_true, true_and]
        by_cases hyz_ij : y (Fin.natAdd 1 i) = z (Fin.natAdd 1 i) ∧
            y (Fin.natAdd 1 j) = z (Fin.natAdd 1 j)
        · have heq : (fun b => y (Fin.natAdd 1 b)) = (fun b => z (Fin.natAdd 1 b)) :=
            _root_.funext fun b => by
              by_cases hbi : b = i
              · subst hbi; exact hyz_ij.1
              · by_cases hbj : b = j
                · subst hbj; exact hyz_ij.2
                · exact hb b (fun ⟨k, hk⟩ => by fin_cases k <;> [exact hbi hk.symm; exact hbj hk.symm])
          rw [if_pos hyz_ij, if_pos heq]
        · rw [if_neg hyz_ij, if_neg (fun heq => hyz_ij ⟨congrFun heq i, congrFun heq j⟩)]
      · have hz0 : z 0 = true := by rw [← h0, hy0]
        simp only [↓reduceIte, hz0, Bool.and_true, h0, eq_self_iff_true, true_and]
        rw [if_pos hb, hcnot_apply]
    · have hnb : ¬ (∀ b : Fin w, b ∉ Set.range (wire2 i j hij) → y (Fin.natAdd 1 b) = z (Fin.natAdd 1 b)) :=
        fun hb => hc (hiff.mp hb)
      rw [if_neg hc]
      cases hy0 : y 0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_neg (fun heq => hnb fun b _ => congrFun heq b)]
      · simp only [↓reduceIte]
        rw [if_neg hnb]
  · simp [h0]

/-! #### 6.1 Small 2-qubit and 3-qubit Controlled Gate Identities -/

lemma act_controlled2_ket (M : Matrix Bool Bool ℂ) (y : Qubits 2) :
    act ((controlled M).submatrix q2Equiv q2Equiv) (ket y) =
      if y 0 then M false (y 1) • ket (Function.update y 1 false) +
          M true (y 1) • ket (Function.update y 1 true)
      else ket y := by
  apply WithLp.ofLp_injective; funext z
  simp only [act, ket, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, Matrix.submatrix_apply,
    controlled, Matrix.of_apply, q2Equiv, Equiv.coe_fn_mk, PiLp.single_apply]
  change (∑ x : Qubits 2, (if z 0 = x 0 then
      (if z 0 then M (z 1) (x 1) else (1 : Matrix Bool Bool ℂ) (z 1) (x 1)) else 0) *
      (if x = y then 1 else 0)) = _
  rw [Finset.sum_eq_single y]
  · simp only [↓reduceIte, mul_one]
    cases hy0 : y 0
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hz_eq : z = y ↔ z 0 = false ∧ z 1 = y 1 := by
        constructor
        · intro h; subst h; exact ⟨hy0, rfl⟩
        · rintro ⟨h0, h1⟩; ext i; fin_cases i <;> simp [h0, hy0, h1]
      by_cases hz0 : z 0 = false
      · cases hz1 : z 1 <;> cases hy1 : y 1 <;> simp [hz0, hy0, hz1, hy1, hz_eq, Matrix.one_apply]
      · have hne : z ≠ y := fun h => hz0 (by rw [h, hy0])
        simp [hz0, hne]
    · simp only [↓reduceIte, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      by_cases hz0 : z 0 = true
      · have hzf : z = Function.update y 1 false ↔ z 1 = false := by
          constructor
          · intro h; rw [h, Function.update_self]
          · intro h; ext i; fin_cases i <;> [simp [hz0, hy0]; simp [h]]
        have hzt : z = Function.update y 1 true ↔ z 1 = true := by
          constructor
          · intro h; rw [h, Function.update_self]
          · intro h; ext i; fin_cases i <;> [simp [hz0, hy0]; simp [h]]
        cases hz1 : z 1 <;> simp [hz0, hz1, hzf, hzt]
      · have hnf : z ≠ Function.update y 1 false := fun h =>
          hz0 (by rw [h, Function.update_of_ne (by decide), hy0])
        have hnt : z ≠ Function.update y 1 true := fun h =>
          hz0 (by rw [h, Function.update_of_ne (by decide), hy0])
        simp [hz0, hnf, hnt]
  · intro x _ hx; simp [hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma controlled_x_eq :
    ((controlled pauliX).submatrix q2Equiv q2Equiv) = cnot.submatrix q2Equiv q2Equiv := by
  ext y z
  simp only [Matrix.submatrix_apply, q2Equiv, Equiv.coe_fn_mk, controlled, Matrix.of_apply, cnot, pauliX]
  cases hy0 : y 0 <;> cases hz0 : z 0 <;> cases hy1 : y 1 <;> cases hz1 : z 1 <;>
    simp [Matrix.one_apply]

private def sAdjMat : Matrix Bool Bool ℂ := phaseS * phaseS * phaseS

private def chA : Matrix Bool Bool ℂ := phaseS * hadamard * gateT.conjTranspose * hadamard * sAdjMat

lemma chA_conj :
    phaseS * hadamard * gateT * hadamard * sAdjMat = chA.conjTranspose := by
  have hs3 : sAdjMat.conjTranspose = phaseS := by
    unfold sAdjMat
    rw [phaseS_cube, Matrix.conjTranspose_conjTranspose]
  have hss : phaseS.conjTranspose = sAdjMat := phaseS_cube.symm
  unfold chA
  simp only [Matrix.conjTranspose_mul, hs3, hadamard_conjTranspose, Matrix.conjTranspose_conjTranspose,
    hss, Matrix.mul_assoc]

lemma chA_mul_conj : chA * chA.conjTranspose = 1 := by
  have h1 : chA * chA.conjTranspose =
      (phaseS * hadamard * gateT.conjTranspose * hadamard * (phaseS * phaseS * phaseS)) *
      (phaseS * hadamard * gateT * hadamard * (phaseS * phaseS * phaseS)) := by
    rw [← chA_conj]; rfl
  rw [h1]
  have h2 : (phaseS * hadamard * gateT.conjTranspose * hadamard * (phaseS * phaseS * phaseS)) *
      (phaseS * hadamard * gateT * hadamard * (phaseS * phaseS * phaseS)) =
      phaseS * hadamard * gateT.conjTranspose * hadamard *
        ((phaseS * phaseS * phaseS) * phaseS) *
        hadamard * gateT * hadamard * (phaseS * phaseS * phaseS) := by
    simp only [Matrix.mul_assoc]
  rw [h2, phaseS_cube]
  have hs_l : phaseS.conjTranspose * phaseS = 1 := by
    ext a b; cases a <;> cases b <;> simp [phaseS, Matrix.mul_apply]
  have ht_l : gateT.conjTranspose * gateT = 1 := by
    ext a b; cases a <;> cases b <;> simp [gateT, Matrix.mul_apply]
    rw [← Complex.exp_conj, ← Complex.exp_add]
    convert Complex.exp_zero
    simp [map_div₀, map_mul, map_ofNat]; ring
  rw [hs_l, Matrix.mul_one, Matrix.mul_assoc _ hadamard hadamard, hadamard_mul_self, Matrix.mul_one]
  rw [Matrix.mul_assoc _ gateT.conjTranspose gateT, ht_l, Matrix.mul_one]
  rw [Matrix.mul_assoc _ hadamard hadamard, hadamard_mul_self, Matrix.mul_one]
  simpa only [Matrix.mul_assoc] using phaseS_unitary

lemma chA_mul_x_mul_conj : chA * pauliX * chA.conjTranspose = hadamard := by
  have h1 : chA * pauliX * chA.conjTranspose =
      (phaseS * hadamard * gateT.conjTranspose * hadamard * (phaseS * phaseS * phaseS)) *
      pauliX * (phaseS * hadamard * gateT * hadamard * (phaseS * phaseS * phaseS)) := by
    rw [← chA_conj]; rfl
  rw [h1]
  have h2 : (phaseS * hadamard * gateT.conjTranspose * hadamard * (phaseS * phaseS * phaseS)) *
      pauliX * (phaseS * hadamard * gateT * hadamard * (phaseS * phaseS * phaseS)) =
      phaseS * (hadamard * (gateT.conjTranspose * (hadamard * ((phaseS * phaseS * phaseS) * pauliX * phaseS) * hadamard) * gateT) * hadamard) * (phaseS * phaseS * phaseS) := by
    simp only [Matrix.mul_assoc]
  rw [h2]
  have hsxs : (phaseS * phaseS * phaseS) * pauliX * phaseS = -pauliY := by
    ext a b; cases a <;> cases b <;> simp [phaseS, pauliX, pauliY, Matrix.mul_apply]
  have hhyh : hadamard * (-pauliY) * hadamard = pauliY := by
    have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    ext a b; cases a <;> cases b <;>
      simp [hadamard, pauliY, Matrix.mul_apply, Fintype.sum_bool] <;>
      field_simp <;> simp [h2'] <;> ring
  have htyt : gateT.conjTranspose * pauliY * gateT =
      Matrix.of fun a b => if a = b then 0 else if a then
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + Complex.I) else ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 - Complex.I) := by
    have hexp : Complex.exp (Complex.I * ↑Real.pi / 4) =
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
      rw [show Complex.I * ↑Real.pi / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_pi_div_four, Real.sin_pi_div_four]
    ext a b; cases a <;> cases b <;>
      simp [gateT, pauliY, Matrix.mul_apply, hexp] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have hh_tyt_h : hadamard * (gateT.conjTranspose * pauliY * gateT) * hadamard =
      Matrix.of fun a b : Bool => match a, b with
        | false, false => ((Real.sqrt 2 : ℂ)⁻¹)
        | false, true => ((Real.sqrt 2 : ℂ)⁻¹) * Complex.I
        | true, false => -((Real.sqrt 2 : ℂ)⁻¹) * Complex.I
        | true, true => -((Real.sqrt 2 : ℂ)⁻¹) := by
    rw [htyt]
    have h2' : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    ext a b; cases a <;> cases b <;>
      simp [hadamard, Matrix.mul_apply, Fintype.sum_bool] <;>
      field_simp <;> simp [h2'] <;> ring
  rw [hsxs, hhyh, hh_tyt_h]
  ext a b; cases a <;> cases b <;>
    simp [phaseS, hadamard, Matrix.mul_apply, Fintype.sum_bool] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma circUnitary_cons2 {n : ℕ} (g₁ g₂ : Instr n) (c : List (Instr n)) :
    circUnitary (g₁ :: g₂ :: c) = circUnitary (g₂ :: c) * circUnitary [g₁] :=
  circUnitary_cons _ _

private lemma q1_embed_mul {n : ℕ} (A B : Matrix Bool Bool ℂ) (i : Fin n) :
    embedOp (A.submatrix q1Equiv q1Equiv) (wire1 i) *
      embedOp (B.submatrix q1Equiv q1Equiv) (wire1 i) =
      embedOp ((A * B).submatrix q1Equiv q1Equiv) (wire1 i) := by
  rw [← embedOp_mul, submatrix_equiv_mul]

lemma controlled_h_circ2 :
    circUnitary ([.s 1, .s 1, .s 1, .h 1, .t 1, .h 1, .s 1, .cnot 0 1 (by decide),
        .s 1, .s 1, .s 1, .h 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .h 1, .s 1] : List (Instr 2)) =
      (controlled hadamard).submatrix q2Equiv q2Equiv := by
  have hc1 : circUnitary ([.s 1, .s 1, .s 1, .h 1, .t 1, .h 1, .s 1] : List (Instr 2)) =
      embedOp (chA.conjTranspose.submatrix q1Equiv q1Equiv) (wire1 1) := by
    rw [← chA_conj]
    simp only [circUnitary_cons2, circUnitary_s 1, circUnitary_h 1, circUnitary_t 1,
      q1_embed_mul, Matrix.mul_assoc, sAdjMat]
  have ht7 : circUnitary ([.t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1] : List (Instr 2)) =
      embedOp (gateT.conjTranspose.submatrix q1Equiv q1Equiv) (wire1 1) := by
    simp only [circUnitary_cons2, circUnitary_t 1, q1_embed_mul]
    rw [gateT_seven]
  have hc3 : circUnitary ([.s 1, .s 1, .s 1, .h 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .h 1, .s 1] : List (Instr 2)) =
      embedOp (chA.submatrix q1Equiv q1Equiv) (wire1 1) := by
    have hsp : ([.s 1, .s 1, .s 1, .h 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .h 1, .s 1] : List (Instr 2)) =
        [.s 1, .s 1, .s 1] ++ [.h 1] ++ [.t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1] ++ [.h 1, .s 1] := rfl
    rw [hsp, circUnitary_append, circUnitary_append, circUnitary_append, ht7]
    simp only [circUnitary_cons2, circUnitary_s 1, circUnitary_h 1, q1_embed_mul]
    rw [← sAdjMat]
    simp only [← Matrix.mul_assoc]
    rfl
  have hc2 : circUnitary ([.cnot 0 1 (by decide)] : List (Instr 2)) = cnot.submatrix q2Equiv q2Equiv := by
    rw [circUnitary_cnot]
    ext y z
    rw [embedOp2_apply, if_pos]
    · rfl
    · intro a ha
      rcases a with ⟨k, hk⟩
      match k with
      | 0 => exact absurd ⟨0, rfl⟩ ha
      | 1 => exact absurd ⟨1, Fin.ext rfl⟩ ha
      | n + 2 => omega
  have hfull_sp : ([.s 1, .s 1, .s 1, .h 1, .t 1, .h 1, .s 1, .cnot 0 1 (by decide),
      .s 1, .s 1, .s 1, .h 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .h 1, .s 1] : List (Instr 2)) =
      [.s 1, .s 1, .s 1, .h 1, .t 1, .h 1, .s 1] ++ [.cnot 0 1 (by decide)] ++
      [.s 1, .s 1, .s 1, .h 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .h 1, .s 1] := rfl
  rw [hfull_sp, circUnitary_append, circUnitary_append, hc1, hc2, hc3]
  apply matrix_eq_of_act_ket
  intro y
  rw [act_mul, act_mul, act_controlled2_ket]
  have hlhs_false : y 0 = false →
      act (embedOp (chA.submatrix q1Equiv q1Equiv) (wire1 1))
        (act (cnot.submatrix q2Equiv q2Equiv)
          (act (embedOp (chA.conjTranspose.submatrix q1Equiv q1Equiv) (wire1 1)) (ket y))) =
      ket y := by
    intro hy0
    rw [act_embedOp1_ket, act_add, act_smul, act_smul]
    have hupd0 : ∀ v : Bool, (Function.update y 1 v) 0 = false := fun v => by
      rw [Function.update_of_ne (by decide), hy0]
    have hc_f : act (cnot.submatrix q2Equiv q2Equiv) (ket (Function.update y 1 false)) =
        ket (Function.update y 1 false) := by
      rw [← hc2, act_cnot_ket, hupd0, Bool.xor_false, Function.update_eq_self]
    have hc_t : act (cnot.submatrix q2Equiv q2Equiv) (ket (Function.update y 1 true)) =
        ket (Function.update y 1 true) := by
      rw [← hc2, act_cnot_ket, hupd0, Bool.xor_false, Function.update_eq_self]
    rw [hc_f, hc_t, act_add, act_smul, act_smul, act_embedOp1_ket, act_embedOp1_ket]
    simp only [Function.update_self, Function.update_idem, smul_add, smul_smul]
    have hm := chA_mul_conj
    have hm00 : chA.conjTranspose false (y 1) * chA false false +
        chA.conjTranspose true (y 1) * chA false true = (1 : Matrix Bool Bool ℂ) false (y 1) := by
      simpa [Matrix.mul_apply, Fintype.sum_bool, add_comm, mul_comm] using congrFun (congrFun hm false) (y 1)
    have hm10 : chA.conjTranspose false (y 1) * chA true false +
        chA.conjTranspose true (y 1) * chA true true = (1 : Matrix Bool Bool ℂ) true (y 1) := by
      simpa [Matrix.mul_apply, Fintype.sum_bool, add_comm, mul_comm] using congrFun (congrFun hm true) (y 1)
    have hrearr : ∀ (a1 a2 b1 b2 : ℂ) (v0 v1 : EuclideanSpace ℂ (Qubits 2)),
        (a1 • v0 + b1 • v1) + (a2 • v0 + b2 • v1) = (a1 + a2) • v0 + (b1 + b2) • v1 := by
      intro a1 a2 b1 b2 v0 v1
      rw [add_assoc, add_left_comm (b1 • v1), ← add_assoc, ← add_smul, ← add_smul]
    rw [hrearr, hm00, hm10]
    cases hy1 : y 1
    · simp [Matrix.one_apply, ← hy1, Function.update_eq_self]
    · simp [Matrix.one_apply, ← hy1, Function.update_eq_self]
  have hlhs_true : y 0 = true →
      act (embedOp (chA.submatrix q1Equiv q1Equiv) (wire1 1))
        (act (cnot.submatrix q2Equiv q2Equiv)
          (act (embedOp (chA.conjTranspose.submatrix q1Equiv q1Equiv) (wire1 1)) (ket y))) =
      hadamard false (y 1) • ket (Function.update y 1 false) +
        hadamard true (y 1) • ket (Function.update y 1 true) := by
    intro hy0
    rw [act_embedOp1_ket, act_add, act_smul, act_smul]
    have hupd0 : ∀ v : Bool, (Function.update y 1 v) 0 = true := fun v => by
      rw [Function.update_of_ne (by decide), hy0]
    have hc_f : act (cnot.submatrix q2Equiv q2Equiv) (ket (Function.update y 1 false)) =
        ket (Function.update y 1 true) := by
      rw [← hc2, act_cnot_ket, hupd0]
      simp [Function.update_idem]
    have hc_t : act (cnot.submatrix q2Equiv q2Equiv) (ket (Function.update y 1 true)) =
        ket (Function.update y 1 false) := by
      rw [← hc2, act_cnot_ket, hupd0]
      simp [Function.update_idem]
    rw [hc_f, hc_t, act_add, act_smul, act_smul, act_embedOp1_ket, act_embedOp1_ket]
    simp only [Function.update_self, Function.update_idem, smul_add, smul_smul]
    have hm := chA_mul_x_mul_conj
    have hm0 : (chA * pauliX * chA.conjTranspose) false (y 1) = hadamard false (y 1) :=
      congrFun (congrFun hm false) (y 1)
    have hm1 : (chA * pauliX * chA.conjTranspose) true (y 1) = hadamard true (y 1) :=
      congrFun (congrFun hm true) (y 1)
    simp only [Matrix.mul_apply, Fintype.sum_bool, pauliX, Matrix.of_apply,
      ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at hm0 hm1
    have hrearr : ∀ (a1 a2 b1 b2 : ℂ) (v0 v1 : EuclideanSpace ℂ (Qubits 2)),
        (a1 • v0 + b1 • v1) + (a2 • v0 + b2 • v1) = (a1 + a2) • v0 + (b1 + b2) • v1 := by
      intro a1 a2 b1 b2 v0 v1
      rw [add_assoc, add_left_comm (b1 • v1), ← add_assoc, ← add_smul, ← add_smul]
    rw [hrearr]
    have hm0' : chA.conjTranspose false (y 1) * chA false true +
        chA.conjTranspose true (y 1) * chA false false = hadamard false (y 1) := by
      rw [mul_comm (chA.conjTranspose false (y 1)), mul_comm (chA.conjTranspose true (y 1)), add_comm]
      exact hm0
    have hm1' : chA.conjTranspose false (y 1) * chA true true +
        chA.conjTranspose true (y 1) * chA true false = hadamard true (y 1) := by
      rw [mul_comm (chA.conjTranspose false (y 1)), mul_comm (chA.conjTranspose true (y 1)), add_comm]
      exact hm1
    rw [hm0', hm1']
  cases hy0 : y 0
  · simp [hy0, hlhs_false hy0]
  · simp [hy0, hlhs_true hy0]

lemma controlled_s_circ2 :
    circUnitary ([.cnot 0 1 (by decide), .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1,
        .cnot 0 1 (by decide), .t 0, .t 1] : List (Instr 2)) =
      (controlled phaseS).submatrix q2Equiv q2Equiv := by
  apply matrix_eq_of_act_ket
  intro y
  have hω4 : Complex.exp (Complex.I * ↑Real.pi / 4) ^ 2 = Complex.I := by
    rw [← Complex.exp_nat_mul]
    rw [show (2 : ℕ) * (Complex.I * ↑Real.pi / 4) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  have hω8 : Complex.exp (Complex.I * ↑Real.pi / 4) ^ 8 = 1 := by
    rw [← Complex.exp_nat_mul]
    rw [show (8 : ℕ) * (Complex.I * ↑Real.pi / 4) = (1 : ℤ) * (2 * ↑Real.pi * Complex.I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I 1
  rw [act_controlled2_ket]
  simp only [act_circ_cons, act_cnot_ket, act_t_ket, act_smul]
  cases hy0 : y 0 <;> cases hy1 : y 1
  · have hu : Function.update y 1 false = y := by ext i; fin_cases i <;> simp [hy0, hy1]
    simp only [hy0, hy1, Bool.xor_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      hu, smul_smul, one_smul, one_mul, mul_one, phaseS, Matrix.diagonal_apply, zero_smul, add_zero]
  · have hu : Function.update y 1 true = y := by ext i; fin_cases i <;> simp [hy0, hy1]
    simp only [hy0, hy1, Bool.xor_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      hu, smul_smul, one_smul, one_mul, mul_one, phaseS, Matrix.diagonal_apply, zero_smul, add_zero,
      mul_assoc]
    rw [show Complex.exp (Complex.I * ↑Real.pi / 4) * (Complex.exp (Complex.I * ↑Real.pi / 4) *
        (Complex.exp (Complex.I * ↑Real.pi / 4) * (Complex.exp (Complex.I * ↑Real.pi / 4) *
        (Complex.exp (Complex.I * ↑Real.pi / 4) * (Complex.exp (Complex.I * ↑Real.pi / 4) *
        (Complex.exp (Complex.I * ↑Real.pi / 4) * Complex.exp (Complex.I * ↑Real.pi / 4))))))) =
        Complex.exp (Complex.I * ↑Real.pi / 4) ^ 8 by ring, hω8, one_smul]
  · have hu : Function.update y 1 false = y := by ext i; fin_cases i <;> simp [hy0, hy1]
    simp only [hy0, hy1, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      Function.update_idem, hu, smul_smul, one_smul, one_mul, mul_one,
      phaseS, Matrix.diagonal_apply, zero_smul, add_zero, mul_assoc]
    rw [show Complex.exp (Complex.I * ↑Real.pi / 4) * (Complex.exp (Complex.I * ↑Real.pi / 4) *
        (Complex.exp (Complex.I * ↑Real.pi / 4) * (Complex.exp (Complex.I * ↑Real.pi / 4) *
        (Complex.exp (Complex.I * ↑Real.pi / 4) * (Complex.exp (Complex.I * ↑Real.pi / 4) *
        (Complex.exp (Complex.I * ↑Real.pi / 4) * Complex.exp (Complex.I * ↑Real.pi / 4))))))) =
        Complex.exp (Complex.I * ↑Real.pi / 4) ^ 8 by ring, hω8, one_smul]
  · have hu : Function.update y 1 true = y := by ext i; fin_cases i <;> simp [hy0, hy1]
    simp only [hy0, hy1, Bool.xor_true, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
      Function.update_self, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),
      Function.update_idem, hu, smul_smul, one_smul, one_mul, mul_one,
      phaseS, Matrix.diagonal_apply, zero_smul, zero_add]
    rw [show Complex.exp (Complex.I * ↑Real.pi / 4) * Complex.exp (Complex.I * ↑Real.pi / 4) =
        Complex.exp (Complex.I * ↑Real.pi / 4) ^ 2 by ring, hω4]

private def toffoli3 : List (Instr 3) :=
  [.h 2, .cnot 1 2 (by decide), .t 2, .t 2, .t 2, .t 2, .t 2, .t 2, .t 2,
   .cnot 0 2 (by decide), .t 2, .cnot 1 2 (by decide), .t 2, .t 2, .t 2, .t 2, .t 2, .t 2, .t 2,
   .cnot 0 2 (by decide), .t 1, .t 2, .cnot 0 1 (by decide), .h 2,
   .t 0, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .cnot 0 1 (by decide)]

lemma toffoli3_eq :
    circUnitary toffoli3 = Matrix.of (fun y z : Qubits 3 =>
      if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then (1 : ℂ) else 0) := by
  let ω := Complex.exp (Complex.I * ↑Real.pi / 4)
  have hω2 : ω ^ 2 = Complex.I := by
    dsimp [ω]; rw [← Complex.exp_nat_mul]
    rw [show (2 : ℕ) * (Complex.I * ↑Real.pi / 4) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_two, Real.sin_pi_div_two]; simp
  have hω4 : ω ^ 4 = -1 := by
    calc ω ^ 4 = (ω ^ 2) ^ 2 := by ring
      _ = Complex.I ^ 2 := by rw [hω2]
      _ = -1 := Complex.I_sq
  have hω6 : ω ^ 6 = -Complex.I := by
    calc ω ^ 6 = ω ^ 4 * ω ^ 2 := by ring
      _ = (-1) * Complex.I := by rw [hω4, hω2]
      _ = -Complex.I := by ring
  have hω8 : ω ^ 8 = 1 := by
    calc ω ^ 8 = (ω ^ 4) ^ 2 := by ring
      _ = (-1) ^ 2 := by rw [hω4]
      _ = 1 := by norm_num
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1 / 2 : ℂ) := by
    have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [← mul_inv, hs]; norm_num
  let cMid : List (Instr 3) :=
    [.cnot 1 2 (by decide), .t 2, .t 2, .t 2, .t 2, .t 2, .t 2, .t 2,
     .cnot 0 2 (by decide), .t 2, .cnot 1 2 (by decide), .t 2, .t 2, .t 2, .t 2, .t 2, .t 2, .t 2,
     .cnot 0 2 (by decide), .t 1, .t 2]
  let cTail : List (Instr 3) :=
    [.t 0, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .cnot 0 1 (by decide)]
  have hω7_mul_ω : ω ^ 7 * ω = 1 := by rw [← pow_succ]; exact hω8
  have hω3_eq : ω ^ 3 = -ω ^ 7 := by
    calc ω ^ 3 = ω ^ 7 * ω ^ 4 := by
          rw [← pow_add]
          calc ω ^ 3 = ω ^ 3 * 1 := (mul_one _).symm
            _ = ω ^ 3 * ω ^ 8 := by rw [hω8]
            _ = ω ^ (7 + 4) := by rw [← pow_add]
      _ = ω ^ 7 * (-1) := by rw [hω4]
      _ = -ω ^ 7 := by ring
  have hv0 : ∀ (a b x : Bool), (![a, b, x] : Qubits 3) 0 = a := fun _ _ _ => rfl
  have hv1 : ∀ (a b x : Bool), (![a, b, x] : Qubits 3) 1 = b := fun _ _ _ => rfl
  have hv2 : ∀ (a b x : Bool), (![a, b, x] : Qubits 3) 2 = x := fun _ _ _ => rfl
  have hupd1 : ∀ (a b x v : Bool), Function.update (![a, b, x] : Qubits 3) 1 v = ![a, v, x] := by
    intro a b x v; ext i; fin_cases i <;> rfl
  have hupd2 : ∀ (a b x v : Bool), Function.update (![a, b, x] : Qubits 3) 2 v = ![a, b, v] := by
    intro a b x v; ext i; fin_cases i <;> rfl
  have hmid : ∀ (a b x : Bool),
      act (circUnitary cMid) (ket ![a, b, x]) =
        (if a && b then (if x then ω ^ 3 else ω ^ 7) else if b then ω else 1) •
          ket ![a, b, x] := by
    intro a b x
    have hω_def : Complex.exp (Complex.I * ↑Real.pi / 4) = ω := rfl
    simp only [cMid, act_circ_cons, act_cnot_ket, act_t_ket,
      act_smul, hupd2, hv0, hv1, hv2, hω_def]
    cases a <;> cases b <;> cases x <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.true_and,
        Bool.false_xor, Bool.true_xor, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
        smul_smul, mul_one, one_mul, one_smul, mul_assoc]
    · have h16 : ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * ω)))))))))))))) =
          (ω ^ 8) ^ 2 := by ring
      rw [h16, hω8, one_pow, one_smul]
    · have h9 : ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * ω))))))) = ω ^ 8 * ω := by ring
      rw [h9, hω8, one_mul]
    · have h9 : ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * ω))))))) = ω ^ 8 * ω := by ring
      rw [h9, hω8, one_mul]
    · have h8' : ω * (ω * (ω * (ω * (ω * (ω * (ω * ω)))))) = ω ^ 8 := by ring
      rw [h8', hω8, one_smul]
    · have h8' : ω * (ω * (ω * (ω * (ω * (ω * (ω * ω)))))) = ω ^ 8 := by ring
      rw [h8', hω8, one_smul]
    · have h15 : ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * (ω * ω))))))))))))) =
          ω ^ 8 * ω ^ 7 := by ring
      rw [h15, hω8, one_mul]
    · have h3' : ω * (ω * ω) = ω ^ 3 := by ring
      rw [h3']
  have hmid2 : ∀ (a b x : Bool),
      act (circUnitary ([.h 2] ++ cMid ++ [.cnot 0 1 (by decide), .h 2])) (ket ![a, b, x]) =
        (if a && b then ω ^ 7 else if b then ω else 1) • ket ![a, xor b a, xor x (a && b)] := by
    intro a b x
    rw [circUnitary_append, circUnitary_append, act_mul, act_mul]
    have hh2 : ∀ (u v w : Bool),
        act (circUnitary [.h 2]) (ket ![u, v, w]) =
          ((Real.sqrt 2 : ℂ)⁻¹) • ket ![u, v, false] +
          (if w then -((Real.sqrt 2 : ℂ)⁻¹) else (Real.sqrt 2 : ℂ)⁻¹) • ket ![u, v, true] := by
      intro u v w
      rw [act_h_ket, hupd2, hupd2, hv2]
    rw [hh2 a b x, act_add, act_smul, act_smul, hmid a b false, hmid a b true]
    rw [act_add, act_smul, act_smul]
    have hch : circUnitary ([.cnot 0 1 (by decide), .h 2] : List (Instr 3)) =
        circUnitary [.h 2] * circUnitary [.cnot 0 1 (by decide)] := by
      rw [circUnitary_cons]
    rw [hch, act_mul, act_smul, act_smul, act_cnot_ket, hupd1, hv0, hv1, hh2 a (xor b a) false]
    rw [act_mul, act_cnot_ket, hupd1, hv0, hv1, hh2 a (xor b a) true]
    have htwor : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) +
        ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 := by
      rw [h2]; norm_num
    let v0 := ket ![a, xor b a, false]
    let v1 := ket ![a, xor b a, true]
    have hcoeff : ∀ (c1 c2 : ℂ),
        c1 • (((Real.sqrt 2 : ℂ)⁻¹) • v0 + ((Real.sqrt 2 : ℂ)⁻¹) • v1) +
        c2 • (((Real.sqrt 2 : ℂ)⁻¹) • v0 + (-((Real.sqrt 2 : ℂ)⁻¹)) • v1) =
        ((c1 + c2) * ((Real.sqrt 2 : ℂ)⁻¹)) • v0 + ((c1 - c2) * ((Real.sqrt 2 : ℂ)⁻¹)) • v1 := by
      intro c1 c2; module
    simp only [smul_smul]
    by_cases hab : a && b
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true,
        Bool.not_false, Bool.not_true, hω3_eq]
      cases x
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.not_false]
        rw [hcoeff]
        have h0 : ((Real.sqrt 2 : ℂ)⁻¹ * ω ^ 7 + (Real.sqrt 2 : ℂ)⁻¹ * -ω ^ 7) * (Real.sqrt 2 : ℂ)⁻¹ = 0 := by
          ring
        have h1 : ((Real.sqrt 2 : ℂ)⁻¹ * ω ^ 7 - (Real.sqrt 2 : ℂ)⁻¹ * -ω ^ 7) * (Real.sqrt 2 : ℂ)⁻¹ = ω ^ 7 := by
          calc _ = 2 * (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * ω ^ 7 := by ring
            _ = ω ^ 7 := by rw [h2]; ring
        rw [h0, h1, zero_smul, zero_add]
      · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_true, Bool.not_true]
        rw [hcoeff]
        have h0 : ((Real.sqrt 2 : ℂ)⁻¹ * ω ^ 7 + -((Real.sqrt 2 : ℂ)⁻¹) * -ω ^ 7) * (Real.sqrt 2 : ℂ)⁻¹ = ω ^ 7 := by
          calc _ = 2 * (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * ω ^ 7 := by ring
            _ = ω ^ 7 := by rw [h2]; ring
        have h1 : ((Real.sqrt 2 : ℂ)⁻¹ * ω ^ 7 - -((Real.sqrt 2 : ℂ)⁻¹) * -ω ^ 7) * (Real.sqrt 2 : ℂ)⁻¹ = 0 := by
          ring
        rw [h0, h1, zero_smul, add_zero]
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
      set s0 : ℂ := if b then ω else 1
      cases x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hcoeff]
        have h0 : ((Real.sqrt 2 : ℂ)⁻¹ * s0 + (Real.sqrt 2 : ℂ)⁻¹ * s0) * (Real.sqrt 2 : ℂ)⁻¹ = s0 := by
          calc _ = 2 * (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * s0 := by ring
            _ = s0 := by rw [h2]; ring
        have h1 : ((Real.sqrt 2 : ℂ)⁻¹ * s0 - (Real.sqrt 2 : ℂ)⁻¹ * s0) * (Real.sqrt 2 : ℂ)⁻¹ = 0 := by
          ring
        rw [h0, h1, zero_smul, add_zero]
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hcoeff]
        have h0 : ((Real.sqrt 2 : ℂ)⁻¹ * s0 + -((Real.sqrt 2 : ℂ)⁻¹) * s0) * (Real.sqrt 2 : ℂ)⁻¹ = 0 := by
          ring
        have h1 : ((Real.sqrt 2 : ℂ)⁻¹ * s0 - -((Real.sqrt 2 : ℂ)⁻¹) * s0) * (Real.sqrt 2 : ℂ)⁻¹ = s0 := by
          calc _ = 2 * (((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹)) * s0 := by ring
            _ = s0 := by rw [h2]; ring
        rw [h0, h1, zero_smul, zero_add]
  have htail : ∀ (a b' z : Bool),
      act (circUnitary cTail) (ket ![a, b', z]) =
        (if a then (if b' then ω ^ 8 else ω) else (if b' then ω ^ 7 else 1)) • ket ![a, xor b' a, z] := by
    intro a b' z
    have hω_def : Complex.exp (Complex.I * ↑Real.pi / 4) = ω := rfl
    simp only [cTail, act_circ_cons, act_cnot_ket, act_t_ket,
      act_smul, hupd1, hv0, hv1, hω_def]
    cases a <;> cases b' <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true,
      smul_smul, one_smul, mul_one, one_mul, mul_assoc]
    · have h7 : ω * (ω * (ω * (ω * (ω * (ω * ω))))) = ω ^ 7 := by ring
      rw [h7]
    · have h8' : ω * (ω * (ω * (ω * (ω * (ω * (ω * ω)))))) = ω ^ 8 := by ring
      rw [h8']
  apply matrix_eq_of_act_ket
  intro y
  have hyvec : y = ![y 0, y 1, y 2] := by ext i; fin_cases i <;> rfl
  have hrhs : act (Matrix.of (fun u v : Qubits 3 =>
      if u 0 = v 0 ∧ u 1 = v 1 ∧ u 2 = xor (v 2) (v 0 && v 1) then (1 : ℂ) else 0)) (ket y) =
      ket ![y 0, y 1, xor (y 2) (y 0 && y 1)] := by
    apply WithLp.ofLp_injective; funext z
    simp only [act, ket, Matrix.mulVec, dotProduct, Matrix.of_apply, WithLp.ofLp_toLp,
      PiLp.single_apply]
    change (∑ x : Qubits 3, (if z 0 = x 0 ∧ z 1 = x 1 ∧ z 2 = xor (x 2) (x 0 && x 1) then (1 : ℂ) else 0) *
        (if x = y then 1 else 0)) = _
    rw [Finset.sum_eq_single y]
    · simp only [↓reduceIte, mul_one]
      have hz_iff : (z 0 = y 0 ∧ z 1 = y 1 ∧ z 2 = xor (y 2) (y 0 && y 1)) ↔
          z = ![y 0, y 1, xor (y 2) (y 0 && y 1)] := by
        constructor
        · rintro ⟨h0, h1, h2'⟩; ext i; fin_cases i <;> simp [h0, h1, h2']
        · intro h; subst h; simp [hv0, hv1, hv2]
      by_cases hz : z = ![y 0, y 1, xor (y 2) (y 0 && y 1)]
      · simp [hz]
      · have hneg : ¬ (z 0 = y 0 ∧ z 1 = y 1 ∧ z 2 = xor (y 2) (y 0 && y 1)) := fun h => hz (hz_iff.mp h)
        simp [hz, hneg]
    · intro x _ hx; simp [hx]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hrhs]
  have hfull_eq : toffoli3 = ([.h 2] ++ cMid ++ [.cnot 0 1 (by decide), .h 2]) ++ cTail := rfl
  conv_lhs => rw [hyvec]
  rw [hfull_eq, circUnitary_append, act_mul, hmid2, act_smul, htail, smul_smul]
  cases hy0 : y 0 <;> cases hy1 : y 1
  · simp [hy0, hy1]
  · simp only [hy0, hy1, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Bool.false_xor, Bool.xor_false, Bool.true_and, Bool.and_true]
    rw [mul_comm, hω7_mul_ω, one_smul]
  · simp only [hy0, hy1, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
      Bool.false_xor, Bool.true_xor, Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.true_eq_false, Bool.true_and, Bool.and_true, one_mul, mul_one]
    rw [hω8, one_smul]
  · simp only [hy0, hy1, Bool.and_self, Bool.false_eq_true, ↓reduceIte, Bool.xor_true,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.xor_false]
    rw [hω7_mul_ω, one_smul]

end QuantumCtrl

section ExactCtrl

def tofStr (e0 e1 e2 : Str) : List Str :=
  let h_t := [false] ++ e2
  let t_0 := [true, true, false] ++ e0
  let t_c := [true, true, false] ++ e1
  let t_t := [true, true, false] ++ e2
  let cx_0c := [true, true, true, true, false] ++ e0 ++ e1
  let cx_0t := [true, true, true, true, false] ++ e0 ++ e2
  let cx_ct := [true, true, true, true, false] ++ e1 ++ e2
  [h_t, cx_ct, t_t, t_t, t_t, t_t, t_t, t_t, t_t, cx_0t, t_t, cx_ct,
    t_t, t_t, t_t, t_t, t_t, t_t, t_t, cx_0t, t_c, t_t, cx_0c, h_t,
    t_0, t_c, t_c, t_c, t_c, t_c, t_c, t_c, cx_0c]

@[fun_prop] theorem tofStr_poly :
    Poly (fun x : (Str × Str) × Str => tofStr x.1.1 x.1.2 x.2) := by
  unfold tofStr
  fun_prop

@[fun_prop] theorem tofStr_comp {α : Type} [Coding α]
    {e0 e1 e2 : α → Str} (h0 : Poly e0) (h1 : Poly e1) (h2 : Poly e2) :
    Poly (fun x => tofStr (e0 x) (e1 x) (e2 x)) :=
  Poly.comp tofStr_poly (Poly.pair (Poly.pair h0 h1) h2)

def ctrlExpandExact (ancEnc insEnc : Str) : List Str :=
  if !(insEnc[0]?.getD false) then
    let et := true :: insEnc.drop 1
    let s_t := [true, false] ++ et
    let h_t := [false] ++ et
    let t_t := [true, true, false] ++ et
    let cx_0t := [true, true, true, true, false, false] ++ et
    [s_t, s_t, s_t, h_t, t_t, h_t, s_t, cx_0t,
      s_t, s_t, s_t, h_t, t_t, t_t, t_t, t_t, t_t, t_t, t_t, h_t, s_t]
  else if !(insEnc[1]?.getD false) then
    let et := true :: insEnc.drop 2
    let cx_0t := [true, true, true, true, false, false] ++ et
    let t_0 := [true, true, false, false]
    let t_t := [true, true, false] ++ et
    [cx_0t, t_t, t_t, t_t, t_t, t_t, t_t, t_t, cx_0t, t_0, t_t]
  else if !(insEnc[2]?.getD false) then
    let et := true :: insEnc.drop 3
    tofStr [false] et ancEnc ++ [[true, true, false] ++ ancEnc] ++ tofStr [false] et ancEnc
  else if !(insEnc[3]?.getD false) then
    let et := true :: insEnc.drop 4
    [[true, true, true, true, false, false] ++ et]
  else
    let rest := insEnc.drop 5
    let idx := rest.findIdx (fun b => !b)
    let ec := true :: rest.take (idx + 1)
    let et := true :: rest.drop (idx + 1)
    tofStr [false] ec et

@[fun_prop] theorem ctrlExpandExact_poly :
    Poly (fun x : Str × Str => ctrlExpandExact x.1 x.2) := by
  unfold ctrlExpandExact
  fun_prop

@[fun_prop] theorem ctrlExpandExact_comp {α : Type} [Coding α]
    {a g : α → Str} (ha : Poly a) (hg : Poly g) :
    Poly (fun x => ctrlExpandExact (a x) (g x)) :=
  Poly.comp ctrlExpandExact_poly (Poly.pair ha hg)

def ctrlBodyExact (s : Str) : Str :=
  let p := parseW s
  let wTotEnc := [true, true] ++ p.1
  let ancEnc := true :: p.1
  let ctrlCs := p.2.flatMap (fun g => ctrlExpandExact ancEnc g)
  wTotEnc ++ (ctrlCs.map (fun _ => true) ++ [false]) ++ ctrlCs.flatMap (fun x => x)

@[fun_prop] theorem ctrlBodyExact_poly : Poly ctrlBodyExact := by
  unfold ctrlBodyExact
  fun_prop

noncomputable def ctrlPostExactProg : PolyProgram id id ctrlBodyExact :=
  (BooleanLists.packProgram.comp ctrlBodyExact_poly.program).comp BooleanLists.unpackProgram

def e2Exact (w : ℕ) (i : Fin w) : Fin 2 ↪ Fin (w + 2) :=
  ⟨![⟨0, by omega⟩, ⟨1 + i.val, by omega⟩], fun a b hab => by
    fin_cases a <;> fin_cases b <;>
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hab
    · rfl
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · rfl⟩

def e3Exact (w : ℕ) (i j : Fin w) (hij : i ≠ j) : Fin 3 ↪ Fin (w + 2) :=
  ⟨![⟨0, by omega⟩, ⟨1 + i.val, by omega⟩, ⟨1 + j.val, by omega⟩], fun a b hab => by
    fin_cases a <;> fin_cases b <;>
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hab
    · rfl
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · rfl
    · exact absurd (Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)) hij
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exact absurd (Fin.ext (by have := congrArg Fin.val hab; dsimp at this; omega)) hij.symm
    · rfl⟩

def eAncExact (w : ℕ) (i : Fin w) : Fin 3 ↪ Fin (w + 2) :=
  ⟨![⟨0, by omega⟩, ⟨1 + i.val, by omega⟩, ⟨1 + w, by omega⟩], fun a b hab => by
    fin_cases a <;> fin_cases b <;>
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hab
    · rfl
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · rfl
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; have := i.isLt; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; omega)
    · exfalso; exact absurd (congrArg Fin.val hab) (by dsimp; have := i.isLt; omega)
    · rfl⟩

def shiftCtrl0Exact (w : ℕ) : Fin (1 + w) ↪ Fin (w + 2) :=
  ⟨fun j => ⟨j.val, by omega⟩, fun _ _ h => Fin.ext (by simpa only [Fin.mk.injEq] using h)⟩

private def chCirc2 : List (Instr 2) :=
  [.s 1, .s 1, .s 1, .h 1, .t 1, .h 1, .s 1, .cnot 0 1 (by decide),
    .s 1, .s 1, .s 1, .h 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .h 1, .s 1]

private def csCirc2 : List (Instr 2) :=
  [.cnot 0 1 (by decide), .t 1, .t 1, .t 1, .t 1, .t 1, .t 1, .t 1,
    .cnot 0 1 (by decide), .t 0, .t 1]

def ctrlInstrExact (w : ℕ) : Instr w → List (Instr (w + 2))
  | .h i => mapCirc (e2Exact w i) chCirc2
  | .s i => mapCirc (e2Exact w i) csCirc2
  | .t i =>
      mapCirc (eAncExact w i) toffoli3 ++
        [.t ⟨1 + w, by omega⟩] ++
        mapCirc (eAncExact w i) toffoli3
  | .x i => mapCirc (e2Exact w i) [.cnot 0 1 (by decide)]
  | .cnot i j hij => mapCirc (e3Exact w i j hij) toffoli3

def ctrlCircExact (w : ℕ) (c : List (Instr w)) : List (Instr (w + 2)) :=
  c.flatMap (ctrlInstrExact w)

lemma e2Exact_0 {w : ℕ} (i : Fin w) : (e2Exact w i 0).val = 0 := rfl
lemma e2Exact_1 {w : ℕ} (i : Fin w) : (e2Exact w i 1).val = 1 + i.val := rfl
lemma e3Exact_0 {w : ℕ} (i j : Fin w) (hij : i ≠ j) : (e3Exact w i j hij 0).val = 0 := rfl
lemma e3Exact_1 {w : ℕ} (i j : Fin w) (hij : i ≠ j) : (e3Exact w i j hij 1).val = 1 + i.val := rfl
lemma e3Exact_2 {w : ℕ} (i j : Fin w) (hij : i ≠ j) : (e3Exact w i j hij 2).val = 1 + j.val := rfl
lemma eAncExact_0 {w : ℕ} (i : Fin w) : (eAncExact w i 0).val = 0 := rfl
lemma eAncExact_1 {w : ℕ} (i : Fin w) : (eAncExact w i 1).val = 1 + i.val := rfl
lemma eAncExact_2 {w : ℕ} (i : Fin w) : (eAncExact w i 2).val = 1 + w := rfl

lemma map_toffoli3_enc {n : ℕ} (e : Fin 3 ↪ Fin n) :
    (mapCirc e toffoli3).map encInstr =
      tofStr (encNat (e 0).val) (encNat (e 1).val) (encNat (e 2).val) := by
  have henc0 : encNat 0 = [false] := rfl
  have henc1 : encNat 1 = [true, false] := rfl
  have henc2 : encNat 2 = [true, true, false] := rfl
  have henc4 : encNat 4 = [true, true, true, true, false] := rfl
  simp only [toffoli3, tofStr, mapCirc, mapInstr, List.map_cons, List.map_nil,
    encInstr, henc0, henc1, henc2, henc4, List.cons_append, List.nil_append, List.append_assoc]

lemma ctrlInstrExact_encInstr {w : ℕ} (g : Instr w) :
    (ctrlInstrExact w g).map encInstr = ctrlExpandExact (encNat (1 + w)) (encInstr g) := by
  have henc1 : encNat 1 = [true, false] := rfl
  have henc2 : encNat 2 = [true, true, false] := rfl
  have henc3 : encNat 3 = [true, true, true, false] := rfl
  have henc4 : encNat 4 = [true, true, true, true, false] := rfl
  cases g with
  | h i =>
    simp only [ctrlInstrExact, chCirc2, mapCirc, mapInstr, List.map_cons, List.map_nil,
      e2Exact_0, e2Exact_1, encNat_one_add, encNat_zero,
      ctrlExpandExact, encInstr, henc1, henc2, henc3, henc4,
      List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, Option.getD_some, Bool.false_eq_true, Bool.not_false, ↓reduceIte,
      List.append_assoc]
  | s i =>
    simp only [ctrlInstrExact, csCirc2, mapCirc, mapInstr, List.map_cons, List.map_nil,
      e2Exact_0, e2Exact_1, encNat_one_add, encNat_zero,
      ctrlExpandExact, encInstr, henc1, henc2, henc3, henc4,
      List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.not_true,
      Bool.false_eq_true, Bool.not_false, ↓reduceIte, List.append_assoc]
  | t i =>
    simp only [ctrlInstrExact, List.map_append, List.map_cons, List.map_nil, map_toffoli3_enc,
      eAncExact_0, eAncExact_1, eAncExact_2, encNat_zero, encNat_one_add,
      ctrlExpandExact, encInstr, henc1, henc2, henc3, henc4,
      List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.not_true,
      Bool.false_eq_true, Bool.not_false, ↓reduceIte, List.append_assoc]
  | x i =>
    simp only [ctrlInstrExact, mapCirc, mapInstr, List.map_cons, List.map_nil,
      e2Exact_0, e2Exact_1, encNat_one_add, encNat_zero,
      ctrlExpandExact, encInstr, henc1, henc2, henc3, henc4,
      List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Bool.not_true,
      Bool.false_eq_true, Bool.not_false, ↓reduceIte, List.append_assoc]
  | cnot i j hij =>
    simp only [ctrlInstrExact, map_toffoli3_enc, e3Exact_0, e3Exact_1, e3Exact_2,
      encNat_zero, encNat_one_add, ctrlExpandExact, encInstr,
      henc1, henc2, henc3, henc4, List.append_assoc, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [findIdx_not_encNat, take_encNat, drop_encNat]

lemma ctrlBodyExact_eq (w : ℕ) (c : List (Instr w)) :
    ctrlBodyExact (encNat w ++ encLayer c) = encNat (w + 2) ++ encLayer (ctrlCircExact w c) := by
  unfold ctrlBodyExact
  rw [parseW_eq]
  dsimp only
  have hw2 : [true, true] ++ encNat w = encNat (w + 2) := by
    rw [show w + 2 = 2 + w by omega, encNat, encNat, List.replicate_add]
    simp [List.append_assoc]
  have hflat : (c.map encInstr).flatMap (fun g => ctrlExpandExact (true :: encNat w) g) =
      (ctrlCircExact w c).map encInstr := by
    rw [List.flatMap_map]
    simp only [ctrlCircExact, List.map_flatMap]
    refine List.flatMap_congr fun g _ => ?_
    rw [← encNat_one_add]
    exact (ctrlInstrExact_encInstr g).symm
  have hid : ∀ xs : List Str, xs.flatMap (fun x => x) = xs.flatten := list_flatMap_id
  rw [hw2, hflat, list_map_true]
  simp only [List.length_map, hid]
  simp [encLayer, encStr, encNat, List.append_assoc]

lemma ctrlInstrExact_length_le {w : ℕ} (g : Instr w) :
    (ctrlInstrExact w g).length ≤ 67 := by
  cases g <;> simp [ctrlInstrExact, chCirc2, csCirc2, toffoli3, mapCirc]

lemma ctrlCircExact_length_le {w : ℕ} (c : List (Instr w)) :
    (ctrlCircExact w c).length ≤ 67 * c.length := by
  induction c with
  | nil => simp [ctrlCircExact]
  | cons g c ih =>
    simp only [ctrlCircExact, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    have hg := ctrlInstrExact_length_le g
    omega

private lemma circUnitary_cnot2 :
    circUnitary ([.cnot 0 1 (by decide)] : List (Instr 2)) = cnot.submatrix q2Equiv q2Equiv := by
  rw [circUnitary_cnot]
  ext y z
  rw [embedOp2_apply, if_pos]
  · rfl
  · intro a ha
    rcases a with ⟨k, hk⟩
    match k with
    | 0 => exact absurd ⟨0, rfl⟩ ha
    | 1 => exact absurd ⟨1, Fin.ext rfl⟩ ha
    | n + 2 => omega

lemma act_sum {ι κ : Type} [Fintype ι] (A : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act A (∑ k ∈ s, f k) = ∑ k ∈ s, act A (f k) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    apply WithLp.ofLp_injective; funext i; simp [act]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, act_add, ih]

lemma act_mapToffoli_ket {n : ℕ} (e : Fin 3 ↪ Fin n) (u : Qubits n) :
    act (embedOp (circUnitary toffoli3) e) (ket u) =
      ket (Function.update u (e 2) (xor (u (e 2)) (u (e 0) && u (e 1)))) := by
  rw [toffoli3_eq]
  apply WithLp.ofLp_injective; funext z
  simp only [act, ket, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, PiLp.single_apply]
  change (∑ x : Qubits n, embedOp (Matrix.of fun a b : Qubits 3 =>
      if a 0 = b 0 ∧ a 1 = b 1 ∧ a 2 = xor (b 2) (b 0 && b 1) then (1 : ℂ) else 0) e z x *
      (if x = u then 1 else 0)) = _
  rw [Finset.sum_eq_single u]
  · simp only [↓reduceIte, mul_one, embedOp, Matrix.of_apply]
    dsimp only [Function.comp_apply]
    have hiff : ((∀ a : Fin n, a ∉ Set.range e → z a = u a) ∧
        (z (e 0) = u (e 0) ∧ z (e 1) = u (e 1) ∧
          z (e 2) = xor (u (e 2)) (u (e 0) && u (e 1)))) ↔
        z = Function.update u (e 2) (xor (u (e 2)) (u (e 0) && u (e 1))) := by
      constructor
      · rintro ⟨hout, h0, h1, h2⟩
        funext a
        by_cases ha : a ∈ Set.range e
        · obtain ⟨k, rfl⟩ := ha
          fin_cases k
          · dsimp only; rw [Function.update_of_ne (e.injective.ne (by decide))]; exact h0
          · dsimp only; rw [Function.update_of_ne (e.injective.ne (by decide))]; exact h1
          · change z (e 2) = Function.update u (e 2) (xor (u (e 2)) (u (e 0) && u (e 1))) (e 2)
            rw [Function.update_self]; exact h2
        · have ha2 : a ≠ e 2 := fun h => ha ⟨2, h.symm⟩
          rw [Function.update_of_ne ha2]
          exact hout a ha
      · intro h
        subst h
        refine ⟨fun a ha => Function.update_of_ne (fun h => ha ⟨2, h.symm⟩) _ _,
          Function.update_of_ne (e.injective.ne (by decide)) _ _,
          Function.update_of_ne (e.injective.ne (by decide)) _ _,
          Function.update_self _ _ _⟩
    by_cases h1 : ∀ a : Fin n, a ∉ Set.range e → z a = u a
    · rw [if_pos h1]
      by_cases h2 : z (e 0) = u (e 0) ∧ z (e 1) = u (e 1) ∧
          z (e 2) = xor (u (e 2)) (u (e 0) && u (e 1))
      · rw [if_pos h2, if_pos (hiff.mp ⟨h1, h2⟩)]
      · rw [if_neg h2, if_neg (fun hz => h2 (hiff.mpr hz).2)]
    · rw [if_neg h1, if_neg (fun hz => h1 (hiff.mpr hz).1)]
  · intro x _ hx; simp [hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

def padVec0 (w : ℕ) (v : EuclideanSpace ℂ (Qubits (1 + w))) :
    EuclideanSpace ℂ (Qubits (w + 2)) :=
  WithLp.toLp 2 (fun y : Qubits (w + 2) =>
    if y ⟨1 + w, by omega⟩ = false then v.ofLp (fun j : Fin (1 + w) => y ⟨j.val, by omega⟩) else 0)

lemma padVec0_add (w : ℕ) (u v : EuclideanSpace ℂ (Qubits (1 + w))) :
    padVec0 w (u + v) = padVec0 w u + padVec0 w v := by
  apply WithLp.ofLp_injective; funext y
  simp only [padVec0, WithLp.ofLp_toLp, PiLp.add_apply]
  split_ifs <;> simp

lemma padVec0_sub (w : ℕ) (u v : EuclideanSpace ℂ (Qubits (1 + w))) :
    padVec0 w (u - v) = padVec0 w u - padVec0 w v := by
  apply WithLp.ofLp_injective; funext y
  simp only [padVec0, WithLp.ofLp_toLp, PiLp.sub_apply]
  split_ifs <;> simp

lemma padVec0_smul (w : ℕ) (c : ℂ) (v : EuclideanSpace ℂ (Qubits (1 + w))) :
    padVec0 w (c • v) = c • padVec0 w v := by
  apply WithLp.ofLp_injective; funext y
  simp only [padVec0, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma padVec0_sum {κ : Type} (w : ℕ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ (Qubits (1 + w))) :
    padVec0 w (∑ k ∈ s, f k) = ∑ k ∈ s, padVec0 w (f k) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    apply WithLp.ofLp_injective; funext y
    simp only [padVec0, WithLp.ofLp_toLp, PiLp.zero_apply]; split_ifs <;> rfl
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, padVec0_add, ih]

lemma padVec0_ket (w : ℕ) (z : Qubits (1 + w)) :
    padVec0 w (ket z) = ket (padTo (w + 2) z) := by
  apply WithLp.ofLp_injective; funext y
  simp only [padVec0, ket, WithLp.ofLp_toLp, PiLp.single_apply]
  have hiff : (y ⟨1 + w, by omega⟩ = false ∧
      (fun j : Fin (1 + w) => y ⟨j.val, by omega⟩) = z) ↔ y = padTo (w + 2) z := by
    constructor
    · rintro ⟨hanc, hpre⟩
      funext a
      have ha_lt := a.isLt
      by_cases ha : a.val < 1 + w
      · simpa [padTo, ha] using congrFun hpre ⟨a.val, ha⟩
      · have ha_eq : a = ⟨1 + w, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [ha_eq, hanc]
        simp [padTo]
    · intro hy
      subst hy
      exact ⟨dif_neg (by dsimp; omega), funext fun j => dif_pos j.isLt⟩
  by_cases hanc : y ⟨1 + w, by omega⟩ = false
  · rw [if_pos hanc]
    by_cases hpre : (fun j : Fin (1 + w) => y ⟨j.val, by omega⟩) = z
    · rw [if_pos hpre, if_pos (hiff.mp ⟨hanc, hpre⟩)]
    · rw [if_neg hpre, if_neg (fun hy => hpre (hiff.mpr hy).2)]
  · rw [if_neg hanc, if_neg (fun hy => hanc (hiff.mpr hy).1)]

private lemma ofLp_sum_eq {ι κ : Type} [DecidableEq ι] (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) (x : ι) :
    (∑ k ∈ s, f k).ofLp x = ∑ k ∈ s, (f k).ofLp x := by
  induction s using Finset.induction with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, PiLp.add_apply, ih]

lemma vec_eq_sum_ket {ι : Type} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    v = ∑ z : ι, v.ofLp z • ket z := by
  apply WithLp.ofLp_injective; funext x
  rw [ofLp_sum_eq]
  simp only [ket, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  change _ = ∑ z : ι, v.ofLp z * (if x = z then 1 else 0)
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hz; simp [hz.symm]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma padVec0_norm (w : ℕ) (v : EuclideanSpace ℂ (Qubits (1 + w))) :
    ‖padVec0 w v‖ = ‖v‖ := by
  have hsq : ‖padVec0 w v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hinv : ∀ z : Qubits (1 + w),
        (fun j : Fin (1 + w) => padTo (w + 2) z ⟨j.val, by omega⟩) = z :=
      fun z => funext fun j => dif_pos j.isLt
    have hs : (∑ y : Qubits (w + 2), ‖(padVec0 w v).ofLp y‖ ^ 2) =
        ∑ y : Qubits (w + 2), if y ⟨1 + w, by omega⟩ = false then
          ‖v.ofLp (fun j : Fin (1 + w) => y ⟨j.val, by omega⟩)‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [padVec0, WithLp.ofLp_toLp]
      split_ifs <;> simp
    rw [hs, ← Finset.sum_filter]
    refine Finset.sum_bij (fun y _ => fun j : Fin (1 + w) => y ⟨j.val, by omega⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y₁ hy₁ y₂ hy₂ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
      funext a
      have ha_lt := a.isLt
      by_cases ha : a.val < 1 + w
      · exact congrFun he ⟨a.val, ha⟩
      · have ha_eq : a = ⟨1 + w, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [ha_eq, hy₁, hy₂]
    · intro z _
      refine ⟨padTo (w + 2) z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, dif_neg (by dsimp; omega)⟩,
        hinv z⟩
    · intro _ _; rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma act_embedOp_shiftCtrl0 (w : ℕ) (M : Matrix (Qubits (1 + w)) (Qubits (1 + w)) ℂ)
    (v : EuclideanSpace ℂ (Qubits (1 + w))) :
    act (embedOp M (shiftCtrl0Exact w)) (padVec0 w v) = padVec0 w (act M v) := by
  apply WithLp.ofLp_injective; funext y
  simp only [act, padVec0, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  have hrng : ∀ x : Qubits (w + 2),
      (∀ a : Fin (w + 2), a ∉ Set.range (shiftCtrl0Exact w) → y a = x a) ↔
        y ⟨1 + w, by omega⟩ = x ⟨1 + w, by omega⟩ := by
    intro x
    constructor
    · intro h
      apply h ⟨1 + w, by omega⟩
      rintro ⟨j, hj⟩
      have hj_lt := j.isLt
      have hv := congrArg Fin.val hj
      change j.val = 1 + w at hv
      omega
    · intro heq a ha
      have ha_lt := a.isLt
      have hge : 1 + w ≤ a.val := by
        by_contra hlt
        have hlt' : a.val < 1 + w := by omega
        exact ha ⟨⟨a.val, hlt'⟩, Fin.ext rfl⟩
      have ha_eq : a = ⟨1 + w, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [ha_eq]; exact heq
  by_cases hyanc : y ⟨1 + w, by omega⟩ = false
  · rw [if_pos hyanc]
    have hsum : (∑ x : Qubits (w + 2), embedOp M (shiftCtrl0Exact w) y x *
        (if x ⟨1 + w, by omega⟩ = false then
          v.ofLp (fun j : Fin (1 + w) => x ⟨j.val, by omega⟩) else 0)) =
        ∑ x ∈ Finset.univ.filter (fun x : Qubits (w + 2) => x ⟨1 + w, by omega⟩ = false),
          M (fun j : Fin (1 + w) => y ⟨j.val, by omega⟩)
            (fun j : Fin (1 + w) => x ⟨j.val, by omega⟩) *
            v.ofLp (fun j : Fin (1 + w) => x ⟨j.val, by omega⟩) := by
      simp only [mul_ite, mul_zero, ← Finset.sum_filter]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [embedOp, Matrix.of_apply, Function.comp_apply]
      rw [if_pos ((hrng x).mpr (hyanc.trans hx.symm))]
      rfl
    rw [hsum]
    refine Finset.sum_bij (fun x _ => fun j : Fin (1 + w) => x ⟨j.val, by omega⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro x₁ hx₁ x₂ hx₂ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      funext a
      have ha_lt := a.isLt
      by_cases ha : a.val < 1 + w
      · exact congrFun he ⟨a.val, ha⟩
      · have ha_eq : a = ⟨1 + w, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [ha_eq, hx₁, hx₂]
    · intro z _
      refine ⟨padTo (w + 2) z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, dif_neg (by dsimp; omega)⟩,
        funext fun j => dif_pos j.isLt⟩
    · intro _ _; rfl
  · rw [if_neg hyanc]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hxanc : x ⟨1 + w, by omega⟩ = false
    · have hne : ¬ (∀ a : Fin (w + 2), a ∉ Set.range (shiftCtrl0Exact w) → y a = x a) := by
        intro h; exact hyanc (((hrng x).mp h).trans hxanc)
      simp only [embedOp, Matrix.of_apply, if_neg hne, zero_mul]
    · simp only [if_neg hxanc, mul_zero]

lemma act_ctrlInstrExact_padVec0 {w : ℕ} (g : Instr w) (v : EuclideanSpace ℂ (Qubits (1 + w))) :
    act (circUnitary (ctrlInstrExact w g)) (padVec0 w v) =
      padVec0 w (act (liftCtrl w (circUnitary [g])) v) := by
  cases g with
  | h i =>
    have hmat : circUnitary (ctrlInstrExact w (.h i)) =
        embedOp (liftCtrl w (circUnitary [.h i])) (shiftCtrl0Exact w) := by
      simp only [ctrlInstrExact, circUnitary_mapCirc, chCirc2]
      rw [controlled_h_circ2, circUnitary_h, liftCtrl_embedOp1, embedOp_embedOp]
      congr 1; ext a; fin_cases a <;> rfl
    rw [hmat, act_embedOp_shiftCtrl0]
  | s i =>
    have hmat : circUnitary (ctrlInstrExact w (.s i)) =
        embedOp (liftCtrl w (circUnitary [.s i])) (shiftCtrl0Exact w) := by
      simp only [ctrlInstrExact, circUnitary_mapCirc, csCirc2]
      rw [controlled_s_circ2, circUnitary_s, liftCtrl_embedOp1, embedOp_embedOp]
      congr 1; ext a; fin_cases a <;> rfl
    rw [hmat, act_embedOp_shiftCtrl0]
  | x i =>
    have hmat : circUnitary (ctrlInstrExact w (.x i)) =
        embedOp (liftCtrl w (circUnitary [.x i])) (shiftCtrl0Exact w) := by
      simp only [ctrlInstrExact, circUnitary_mapCirc]
      rw [circUnitary_cnot2, ← controlled_x_eq, circUnitary_x, liftCtrl_embedOp1, embedOp_embedOp]
      congr 1; ext a; fin_cases a <;> rfl
    rw [hmat, act_embedOp_shiftCtrl0]
  | cnot i j hij =>
    have hmat : circUnitary (ctrlInstrExact w (.cnot i j hij)) =
        embedOp (liftCtrl w (circUnitary [.cnot i j hij])) (shiftCtrl0Exact w) := by
      simp only [ctrlInstrExact, circUnitary_mapCirc]
      rw [toffoli3_eq, circUnitary_cnot, liftCtrl_embedOp2_cnot, embedOp_embedOp]
      congr 1; ext a; fin_cases a <;> rfl
    rw [hmat, act_embedOp_shiftCtrl0]
  | t i =>
    have hketL : ∀ z : Qubits (1 + w),
        act (circUnitary (ctrlInstrExact w (.t i))) (ket (padTo (w + 2) z)) =
          (if z 0 && z ⟨1 + i.val, by omega⟩ then Complex.exp (Complex.I * ↑Real.pi / 4) else 1) •
            ket (padTo (w + 2) z) := by
      intro z
      let y0 : Qubits (w + 2) := padTo (w + 2) z
      have hy0_anc : y0 ⟨1 + w, by omega⟩ = false := dif_neg (by dsimp; omega)
      have hy0_0 : y0 (eAncExact w i 0) = z 0 := by simp [y0, padTo, eAncExact]
      have hy0_1 : y0 (eAncExact w i 1) = z ⟨1 + i.val, by omega⟩ := by
        simp [y0, padTo, eAncExact, i.isLt]
      have he2_eq : eAncExact w i 2 = ⟨1 + w, by omega⟩ := rfl
      have hne0 : (⟨1 + w, by omega⟩ : Fin (w + 2)) ≠ eAncExact w i 0 := fun h => by
        have hv := congrArg Fin.val h
        change 1 + w = (eAncExact w i 0).val at hv
        rw [eAncExact_0] at hv; omega
      have hne1 : (⟨1 + w, by omega⟩ : Fin (w + 2)) ≠ eAncExact w i 1 := fun h => by
        have hv := congrArg Fin.val h
        change 1 + w = (eAncExact w i 1).val at hv
        rw [eAncExact_1] at hv; have := i.isLt; omega
      simp only [ctrlInstrExact, circUnitary_append, act_mul, circUnitary_mapCirc]
      rw [act_mapToffoli_ket (eAncExact w i) y0, he2_eq, hy0_anc, hy0_0, hy0_1, Bool.false_xor]
      rw [act_t_ket ⟨1 + w, by omega⟩, Function.update_self, act_smul, act_mapToffoli_ket]
      rw [he2_eq, Function.update_self, Function.update_of_ne hne0.symm,
        Function.update_of_ne hne1.symm, hy0_0, hy0_1, Bool.xor_self, Function.update_idem,
        show Function.update y0 ⟨1 + w, by omega⟩ false = y0 from
          Function.update_eq_self_iff.mpr hy0_anc.symm]
    have hketR : ∀ z : Qubits (1 + w),
        act (liftCtrl w (circUnitary [.t i])) (ket z) =
          (if z 0 && z ⟨1 + i.val, by omega⟩ then Complex.exp (Complex.I * ↑Real.pi / 4) else 1) •
            ket z := by
      intro z
      rw [circUnitary_t, liftCtrl_embedOp1]
      apply WithLp.ofLp_injective; funext u
      simp only [act, ket, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, PiLp.smul_apply,
        smul_eq_mul, PiLp.single_apply]
      change (∑ x : Qubits (1 + w),
          embedOp ((controlled gateT).submatrix q2Equiv q2Equiv)
            (wire2 0 ⟨1 + i.val, by omega⟩ (by simp [Fin.ext_iff]; omega)) u x * (if x = z then 1 else 0)) = _
      rw [Finset.sum_eq_single z]
      · simp only [↓reduceIte, mul_one, embedOp2_apply, controlled, Matrix.of_apply, gateT,
          Matrix.diagonal_apply]
        by_cases hcon : ∀ a : Fin (1 + w),
            a ∉ Set.range (wire2 0 ⟨1 + i.val, by omega⟩ (by simp [Fin.ext_iff]; omega)) → u a = z a
        · rw [if_pos hcon]
          by_cases hu : u = z
          · subst hu
            cases hz0 : u 0 <;> cases hzi : u ⟨1 + i.val, by omega⟩ <;> simp [hz0, hzi]
          · rw [if_neg hu, mul_zero]
            have hdiff : u 0 ≠ z 0 ∨ u ⟨1 + i.val, by omega⟩ ≠ z ⟨1 + i.val, by omega⟩ := by
              by_contra! h
              apply hu; funext a
              by_cases ha0 : a = 0
              · subst ha0; exact h.1
              · by_cases hai : a = ⟨1 + i.val, by omega⟩
                · subst hai; exact h.2
                · apply hcon a; rintro ⟨k, hk⟩; fin_cases k
                  · exact ha0 hk.symm
                  · exact hai hk.symm
            cases hu0 : u 0 <;> cases hui : u ⟨1 + i.val, by omega⟩ <;>
              cases hz0 : z 0 <;> cases hzi : z ⟨1 + i.val, by omega⟩ <;>
              simp_all [Matrix.one_apply]
        · rw [if_neg hcon]
          have hne : u ≠ z := fun h => hcon (fun _ _ => by subst h; rfl)
          simp [hne]
      · intro x _ hx; simp [hx]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    conv_lhs => rw [vec_eq_sum_ket v]
    conv_rhs => rw [vec_eq_sum_ket v]
    rw [padVec0_sum, act_sum, act_sum, padVec0_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [padVec0_smul, act_smul, padVec0_ket, hketL z, act_smul, hketR z, padVec0_smul,
      padVec0_smul, padVec0_ket]

lemma act_ctrlCircExact_padVec0 {w : ℕ} (c : List (Instr w))
    (v : EuclideanSpace ℂ (Qubits (1 + w))) :
    act (circUnitary (ctrlCircExact w c)) (padVec0 w v) =
      padVec0 w (act (liftCtrl w (circUnitary c)) v) := by
  induction c generalizing v with
  | nil =>
    simp only [ctrlCircExact, List.flatMap_nil, circUnitary, Circuit.unitary]
    change act (1 : Matrix (Qubits (w + 2)) (Qubits (w + 2)) ℂ) (padVec0 w v) =
      padVec0 w (act (liftCtrl w 1) v)
    rw [liftCtrl_one]
    apply WithLp.ofLp_injective; funext y
    simp [act, Matrix.one_apply]
  | cons g c ih =>
    have h1 : ctrlCircExact w (g :: c) = ctrlInstrExact w g ++ ctrlCircExact w c := rfl
    rw [h1, circUnitary_append, act_mul, act_ctrlInstrExact_padVec0, ih,
      circUnitary_cons g c, liftCtrl_mul, act_mul]

lemma padTo_boolAppCode {X : Type} {m w : ℕ} (c : X → Qubits m) (p : Bool × X) :
    padTo (1 + w) (boolAppCode c p) = Fin.append (fun _ : Fin 1 => p.1) (padTo w (c p.2)) := by
  funext a
  refine Fin.addCases (fun b => ?_) (fun j => ?_) a
  · have hb : b = 0 := Subsingleton.elim b 0
    subst hb
    simp only [padTo, boolAppCode, Fin.val_castAdd, Fin.val_zero]
    rw [dif_pos (by omega)]
    change (Fin.append (fun _ : Fin 1 => p.1) (c p.2)) (Fin.castAdd m (0 : Fin 1)) =
      Fin.append (fun _ : Fin 1 => p.1) (padTo w (c p.2)) (Fin.castAdd w (0 : Fin 1))
    rw [Fin.append_left, Fin.append_left]
  · simp only [padTo, boolAppCode, Fin.val_natAdd, Fin.append_right]
    by_cases h : j.val < m
    · rw [dif_pos (by omega), dif_pos h]
      exact Fin.append_right _ _ ⟨j.val, h⟩
    · rw [dif_neg (by omega), dif_neg h]

lemma padTo_padTo_exact {n m k : ℕ} (hnm : n ≤ m) (x : Qubits n) :
    padTo k (padTo m x) = padTo k x := by
  funext i
  dsimp only [padTo]
  by_cases hm : i.val < m <;> by_cases hn : i.val < n <;> simp [hm, hn]
  · omega


end ExactCtrl

/-! ### Part 8: Exact Ancilla-Assisted Sum Combinator (`sumCode`, `sumMat`) -/

section SumComb

def sumInnerExact (pair : Str × Str) : Str :=
  let p0 := parseW pair.1
  let p1 := parseW pair.2
  let wEnc := if p0.1.length ≤ p1.1.length then p1.1 else p0.1
  let wTotEnc := [true, true] ++ wEnc
  let ancEnc := true :: wEnc
  let x0Enc : Str := [true, true, true, false, false]
  let c0Ctrl := p0.2.flatMap (fun g => ctrlExpandExact ancEnc g)
  let c1Ctrl := p1.2.flatMap (fun g => ctrlExpandExact ancEnc g)
  let allCs := [x0Enc] ++ c0Ctrl ++ [x0Enc] ++ c1Ctrl
  wTotEnc ++ (allCs.map (fun _ => true) ++ [false]) ++ allCs.flatMap (fun x => x)

@[fun_prop] theorem sumInnerExact_poly : Poly sumInnerExact := by
  unfold sumInnerExact
  fun_prop

noncomputable def sumPostExactProg : PolyProgram id id (sumInnerExact ∘ unpackPairAux none) :=
  packPairProgram.comp (sumInnerExact_poly.program.comp BooleanLists.unpackProgram)

def shiftPrefix (w W : ℕ) (hw : w ≤ W) : Fin w ↪ Fin W :=
  ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (by simpa only [Fin.mk.injEq] using h)⟩

def sumCircExact (w₀ w₁ : ℕ) (c₀ : List (Instr w₀)) (c₁ : List (Instr w₁)) :
    List (Instr (max w₀ w₁ + 2)) :=
  let W := max w₀ w₁
  let c₀' := mapCirc (shiftPrefix w₀ W (le_max_left _ _)) c₀
  let c₁' := mapCirc (shiftPrefix w₁ W (le_max_right _ _)) c₁
  [.x ⟨0, by omega⟩] ++ ctrlCircExact W c₀' ++ [.x ⟨0, by omega⟩] ++ ctrlCircExact W c₁'

lemma mapInstr_shiftPrefix_encInstr {w W : ℕ} (hw : w ≤ W) (g : Instr w) :
    encInstr (mapInstr (shiftPrefix w W hw) g) = encInstr g := by
  have hval : ∀ i : Fin w, (shiftPrefix w W hw i).val = i.val := fun _ => rfl
  cases g <;> simp [mapInstr, encInstr, hval]

lemma mapCirc_shiftPrefix_encInstr {w W : ℕ} (hw : w ≤ W) (c : List (Instr w)) :
    (mapCirc (shiftPrefix w W hw) c).map encInstr = c.map encInstr := by
  simp only [mapCirc, List.map_map]
  refine List.map_congr_left fun g _ => ?_
  exact mapInstr_shiftPrefix_encInstr hw g

lemma sumInnerExact_eq {w₀ w₁ : ℕ} (c₀ : List (Instr w₀)) (c₁ : List (Instr w₁)) :
    sumInnerExact (encNat w₀ ++ encLayer c₀, encNat w₁ ++ encLayer c₁) =
      encNat (max w₀ w₁ + 2) ++ encLayer (sumCircExact w₀ w₁ c₀ c₁) := by
  unfold sumInnerExact
  rw [parseW_eq, parseW_eq]
  dsimp only
  have hwMax : (if (encNat w₀).length ≤ (encNat w₁).length then encNat w₁ else encNat w₀) =
      encNat (max w₀ w₁) := by
    simp only [encNat_length, Nat.add_le_add_iff_right]
    by_cases h : w₀ ≤ w₁
    · simp [h, Nat.max_eq_right h]
    · simp [h, Nat.max_eq_left (Nat.le_of_not_le h)]
  rw [hwMax]
  set W := max w₀ w₁
  have hw2 : [true, true] ++ encNat W = encNat (W + 2) := by
    rw [show W + 2 = 2 + W by omega, encNat, encNat, List.replicate_add]
    simp [List.append_assoc]
  have hx0 : ([true, true, true, false, false] : Str) =
      encInstr (.x ⟨0, by omega⟩ : Instr (W + 2)) := by
    have h0 : encNat 0 = [false] := rfl
    simp [encInstr, encNat]
  have hc0 : (c₀.map encInstr).flatMap (fun g => ctrlExpandExact (true :: encNat W) g) =
      (ctrlCircExact W (mapCirc (shiftPrefix w₀ W (le_max_left _ _)) c₀)).map encInstr := by
    rw [← mapCirc_shiftPrefix_encInstr (le_max_left w₀ w₁) c₀, List.flatMap_map]
    simp only [ctrlCircExact, List.map_flatMap]
    refine List.flatMap_congr fun g _ => ?_
    rw [← encNat_one_add]
    exact (ctrlInstrExact_encInstr g).symm
  have hc1 : (c₁.map encInstr).flatMap (fun g => ctrlExpandExact (true :: encNat W) g) =
      (ctrlCircExact W (mapCirc (shiftPrefix w₁ W (le_max_right _ _)) c₁)).map encInstr := by
    rw [← mapCirc_shiftPrefix_encInstr (le_max_right w₀ w₁) c₁, List.flatMap_map]
    simp only [ctrlCircExact, List.map_flatMap]
    refine List.flatMap_congr fun g _ => ?_
    rw [← encNat_one_add]
    exact (ctrlInstrExact_encInstr g).symm
  have hid : ∀ xs : List Str, xs.flatMap (fun x => x) = xs.flatten := list_flatMap_id
  rw [hw2, hc0, hc1]
  have hlist : [([true, true, true, false, false] : Str)] ++
      (ctrlCircExact W (mapCirc (shiftPrefix w₀ W (le_max_left _ _)) c₀)).map encInstr ++
      [([true, true, true, false, false] : Str)] ++
      (ctrlCircExact W (mapCirc (shiftPrefix w₁ W (le_max_right _ _)) c₁)).map encInstr =
      (sumCircExact w₀ w₁ c₀ c₁).map encInstr := by
    rw [hx0]
    dsimp only [sumCircExact, W]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rw [hlist, list_map_true]
  simp only [List.length_map, hid]
  dsimp only [W]
  simp [encLayer, encStr, encNat, List.append_assoc]

lemma sumCircExact_length_le {w₀ w₁ : ℕ} (c₀ : List (Instr w₀)) (c₁ : List (Instr w₁)) :
    (sumCircExact w₀ w₁ c₀ c₁).length ≤ 2 + 67 * (c₀.length + c₁.length) := by
  dsimp only [sumCircExact]
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h0 : (ctrlCircExact (max w₀ w₁) (mapCirc (shiftPrefix w₀ (max w₀ w₁) (le_max_left _ _)) c₀)).length ≤
      67 * c₀.length := by
    simpa [mapCirc, List.length_map] using
      ctrlCircExact_length_le (mapCirc (shiftPrefix w₀ (max w₀ w₁) (le_max_left _ _)) c₀)
  have h1 : (ctrlCircExact (max w₀ w₁) (mapCirc (shiftPrefix w₁ (max w₀ w₁) (le_max_right _ _)) c₁)).length ≤
      67 * c₁.length := by
    simpa [mapCirc, List.length_map] using
      ctrlCircExact_length_le (mapCirc (shiftPrefix w₁ (max w₀ w₁) (le_max_right _ _)) c₁)
  omega

def padVecW {w W : ℕ} (hw : w ≤ W) (v : EuclideanSpace ℂ (Qubits w)) :
    EuclideanSpace ℂ (Qubits W) :=
  WithLp.toLp 2 (fun y : Qubits W =>
    if ∀ a : Fin W, w ≤ a.val → y a = false then
      v.ofLp (fun j : Fin w => y ⟨j.val, by omega⟩)
    else 0)

lemma padVecW_sub {w W : ℕ} (hw : w ≤ W) (u v : EuclideanSpace ℂ (Qubits w)) :
    padVecW hw (u - v) = padVecW hw u - padVecW hw v := by
  apply WithLp.ofLp_injective; funext y
  simp only [padVecW, WithLp.ofLp_toLp, PiLp.sub_apply]
  split_ifs <;> simp

lemma padVecW_norm {w W : ℕ} (hw : w ≤ W) (v : EuclideanSpace ℂ (Qubits w)) :
    ‖padVecW hw v‖ = ‖v‖ := by
  have hsq : ‖padVecW hw v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    have hs : (∑ y : Qubits W, ‖(padVecW hw v).ofLp y‖ ^ 2) =
        ∑ y : Qubits W, if ∀ a : Fin W, w ≤ a.val → y a = false then
          ‖v.ofLp (fun j : Fin w => y ⟨j.val, by omega⟩)‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [padVecW, WithLp.ofLp_toLp]
      split_ifs <;> simp
    rw [hs, ← Finset.sum_filter]
    refine Finset.sum_bij (fun y _ => fun j : Fin w => y ⟨j.val, by omega⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y₁ hy₁ y₂ hy₂ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
      funext a
      by_cases ha : a.val < w
      · exact congrFun he ⟨a.val, ha⟩
      · exact (hy₁ a (by omega)).trans (hy₂ a (by omega)).symm
    · intro z _
      refine ⟨padTo W z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha => ?_⟩, ?_⟩
      · exact dif_neg (by omega)
      · funext j; exact dif_pos j.isLt
    · intro _ _; rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma act_embedOp_shiftPrefix {w W : ℕ} (hw : w ≤ W) (M : Matrix (Qubits w) (Qubits w) ℂ)
    (v : EuclideanSpace ℂ (Qubits w)) :
    act (embedOp M (shiftPrefix w W hw)) (padVecW hw v) = padVecW hw (act M v) := by
  apply WithLp.ofLp_injective; funext y
  simp only [act, padVecW, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  have hrng : ∀ x : Qubits W,
      (∀ a : Fin W, a ∉ Set.range (shiftPrefix w W hw) → y a = x a) ↔
        ∀ a : Fin W, w ≤ a.val → y a = x a := by
    intro x
    refine forall_congr' fun a => ?_
    have hiff : a ∉ Set.range (shiftPrefix w W hw) ↔ w ≤ a.val := by
      constructor
      · intro h
        by_contra hlt
        exact h ⟨⟨a.val, by omega⟩, Fin.ext rfl⟩
      · intro hge ⟨j, hj⟩
        have hj_lt := j.isLt
        have hv := congrArg Fin.val hj
        change j.val = a.val at hv
        omega
    rw [hiff]
  by_cases hyp : ∀ a : Fin W, w ≤ a.val → y a = false
  · rw [if_pos hyp]
    have hsum : (∑ x : Qubits W, embedOp M (shiftPrefix w W hw) y x *
        (if ∀ a : Fin W, w ≤ a.val → x a = false then
          v.ofLp (fun j : Fin w => x ⟨j.val, by omega⟩) else 0)) =
        ∑ x ∈ Finset.univ.filter (fun x : Qubits W => ∀ a : Fin W, w ≤ a.val → x a = false),
          M (fun j : Fin w => y ⟨j.val, by omega⟩) (fun j : Fin w => x ⟨j.val, by omega⟩) *
            v.ofLp (fun j : Fin w => x ⟨j.val, by omega⟩) := by
      simp only [mul_ite, mul_zero, ← Finset.sum_filter]
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [embedOp, Matrix.of_apply, Function.comp_apply]
      rw [if_pos ((hrng x).mpr fun a ha => (hyp a ha).trans (hx a ha).symm)]
      rfl
    rw [hsum]
    refine Finset.sum_bij (fun x _ => fun j : Fin w => x ⟨j.val, by omega⟩)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro x₁ hx₁ x₂ hx₂ he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      funext a
      by_cases ha : a.val < w
      · exact congrFun he ⟨a.val, ha⟩
      · exact (hx₁ a (by omega)).trans (hx₂ a (by omega)).symm
    · intro z _
      refine ⟨padTo W z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a ha => dif_neg (by omega)⟩,
        funext fun j => dif_pos j.isLt⟩
    · intro _ _; rfl
  · rw [if_neg hyp]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hxp : ∀ a : Fin W, w ≤ a.val → x a = false
    · have hne : ¬ (∀ a : Fin W, a ∉ Set.range (shiftPrefix w W hw) → y a = x a) := by
        intro h; apply hyp; intro a ha
        exact ((hrng x).mp h a ha).trans (hxp a ha)
      simp only [embedOp, Matrix.of_apply, if_neg hne, zero_mul]
    · simp only [if_neg hxp, mul_zero]

lemma embedVec_padTo_W {X : Type} [Fintype X] {m w W : ℕ} (hmw : m ≤ w) (hw : w ≤ W)
    (c : X → Qubits m) (φ : EuclideanSpace ℂ X) :
    embedVec (fun x => padTo W (c x)) φ = padVecW hw (embedVec (fun x => padTo w (c x)) φ) := by
  apply WithLp.ofLp_injective; funext y
  simp only [embedVec, padVecW, WithLp.ofLp_toLp]
  by_cases hyp : ∀ a : Fin W, w ≤ a.val → y a = false
  · rw [if_pos hyp]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hiff : padTo W (c x) = y ↔
        padTo w (c x) = (fun j : Fin w => y ⟨j.val, by omega⟩) := by
      constructor
      · intro h; funext j
        have hj := congrFun h ⟨j.val, by omega⟩
        simpa [padTo] using hj
      · intro h; funext a
        by_cases ha : a.val < w
        · simpa [padTo, ha] using congrFun h ⟨a.val, ha⟩
        · rw [hyp a (by omega)]
          exact dif_neg (by omega)
    by_cases h : padTo W (c x) = y
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  · rw [if_neg hyp]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : padTo W (c x) ≠ y := by
      intro h; apply hyp; intro a ha
      rw [← h]; exact dif_neg (by omega)
    rw [if_neg hne]

lemma padCirc_implements {X Y : Type} [Fintype X] [Fintype Y] {inW outW w W : ℕ}
    (hin : inW ≤ w) (hout : outW ≤ w) (hw : w ≤ W)
    (cx : X → Qubits inW) (cy : Y → Qubits outW)
    (c : List (Instr w)) (Φ : Matrix Y X ℂ) (ε : ℝ)
    (himp : Implements (circUnitary c) (fun x => padTo w (cx x)) (fun y => padTo w (cy y)) Φ ε) :
    Implements (circUnitary (mapCirc (shiftPrefix w W hw) c))
      (fun x => padTo W (cx x)) (fun y => padTo W (cy y)) Φ ε := by
  intro φ
  rw [circUnitary_mapCirc, embedVec_padTo_W hin hw cx φ, embedVec_padTo_W hout hw cy _,
    act_embedOp_shiftPrefix, ← padVecW_sub, padVecW_norm]
  exact himp φ

def liftBool (W : ℕ) (b : Bool) (u : EuclideanSpace ℂ (Qubits W)) :
    EuclideanSpace ℂ (Qubits (1 + W)) :=
  WithLp.toLp 2 (fun y : Qubits (1 + W) =>
    if y 0 = b then u.ofLp (fun j : Fin W => y (Fin.natAdd 1 j)) else 0)

lemma liftBool_norm_sq (W : ℕ) (u₀ u₁ : EuclideanSpace ℂ (Qubits W)) :
    ‖liftBool W false u₀ + liftBool W true u₁‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hsp : (∑ y : Qubits (1 + W), ‖(liftBool W false u₀ + liftBool W true u₁).ofLp y‖ ^ 2) =
      ∑ p ∈ Finset.univ, ‖(liftBool W false u₀ + liftBool W true u₁).ofLp ((splitCtrl W).symm p)‖ ^ 2 :=
    (Fintype.sum_equiv (splitCtrl W).symm _ _ fun _ => rfl).symm
  rw [hsp, Fintype.sum_prod_type, Fintype.sum_bool]
  have happ0 : ∀ (b : Bool) (x : Qubits W),
      (Fin.append (fun _ : Fin 1 => b) x : Qubits (1 + W)) 0 = b :=
    fun b x => Fin.append_left (fun _ : Fin 1 => b) x 0
  have happt : ∀ (b : Bool) (x : Qubits W) (j : Fin W),
      (Fin.append (fun _ : Fin 1 => b) x : Qubits (1 + W)) (Fin.natAdd 1 j) = x j :=
    fun b x j => Fin.append_right (fun _ : Fin 1 => b) x j
  have ht : (∑ x : Qubits W,
      ‖(liftBool W false u₀ + liftBool W true u₁).ofLp ((splitCtrl W).symm (true, x))‖ ^ 2) =
      ∑ x : Qubits W, ‖u₁.ofLp x‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [PiLp.add_apply, liftBool, WithLp.ofLp_toLp, splitCtrl, Equiv.coe_fn_symm_mk,
      happ0, happt, Bool.true_eq_false, ↓reduceIte, zero_add]
  have hf : (∑ x : Qubits W,
      ‖(liftBool W false u₀ + liftBool W true u₁).ofLp ((splitCtrl W).symm (false, x))‖ ^ 2) =
      ∑ x : Qubits W, ‖u₀.ofLp x‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [PiLp.add_apply, liftBool, WithLp.ofLp_toLp, splitCtrl, Equiv.coe_fn_symm_mk,
      happ0, happt, Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [ht, hf, add_comm]

lemma act_X0_liftBool (W : ℕ) (b : Bool) (u : EuclideanSpace ℂ (Qubits W)) :
    act (circUnitary ([.x ⟨0, by omega⟩] : List (Instr (1 + W)))) (liftBool W b u) =
      liftBool W (!b) u := by
  rw [circUnitary_x]
  apply WithLp.ofLp_injective; funext y
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, liftBool]
  let z0 : Qubits (1 + W) := Function.update y ⟨0, by omega⟩ (! y ⟨0, by omega⟩)
  rw [Finset.sum_eq_single z0]
  · rw [embedOp1_apply]
    have hcon : ∀ a : Fin (1 + W), a ∉ Set.range (wire1 (⟨0, by omega⟩ : Fin (1 + W))) → y a = z0 a := by
      intro a ha
      have hne : a ≠ ⟨0, by omega⟩ := fun h => ha ⟨0, h.symm⟩
      exact (Function.update_of_ne hne _ y).symm
    rw [if_pos hcon]
    have hz00 : z0 ⟨0, by omega⟩ = ! y ⟨0, by omega⟩ := Function.update_self _ _ _
    have hpx : pauliX (y ⟨0, by omega⟩) (z0 ⟨0, by omega⟩) = 1 := by
      rw [hz00]; cases hy : y ⟨0, by omega⟩ <;> simp [pauliX]
    have h0eq : (⟨0, by omega⟩ : Fin (1 + W)) = 0 := rfl
    have hj_ne : ∀ j : Fin W, Fin.natAdd 1 j ≠ (⟨0, by omega⟩ : Fin (1 + W)) := by
      intro j h
      have hv := congrArg Fin.val h
      simp [Fin.val_natAdd] at hv
    have htail : (fun j : Fin W => z0 (Fin.natAdd 1 j)) = (fun j : Fin W => y (Fin.natAdd 1 j)) :=
      funext fun j => Function.update_of_ne (hj_ne j) _ y
    have hbool : (z0 0 = b) ↔ (y 0 = !b) := by
      rw [← h0eq, hz00]
      cases y ⟨0, by omega⟩ <;> cases b <;> decide
    rw [hpx, one_mul, htail]
    by_cases hb : y 0 = !b
    · rw [if_pos (hbool.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (hbool.mp h)), if_neg hb]
  · intro x _ hx
    rw [embedOp1_apply]
    by_cases hcon : ∀ a : Fin (1 + W), a ∉ Set.range (wire1 (⟨0, by omega⟩ : Fin (1 + W))) → y a = x a
    · rw [if_pos hcon]
      have hx0 : x ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by
        by_contra hne
        apply hx; funext a
        by_cases ha : a = ⟨0, by omega⟩
        · rw [ha]
          dsimp only [z0]
          rw [Function.update_self]
          cases hxa : x ⟨0, by omega⟩ <;> cases hya : y ⟨0, by omega⟩ <;> simp_all
        · dsimp only [z0]
          rw [Function.update_of_ne ha]
          exact (hcon a fun ⟨_, hk⟩ => ha hk.symm).symm
      rw [hx0]; cases y ⟨0, by omega⟩ <;> simp [pauliX]
    · rw [if_neg hcon, zero_mul]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma act_liftCtrl_liftBool_false (W : ℕ) (A : Matrix (Qubits W) (Qubits W) ℂ)
    (u : EuclideanSpace ℂ (Qubits W)) :
    act (liftCtrl W A) (liftBool W false u) = liftBool W false u := by
  apply WithLp.ofLp_injective; funext y
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, liftBool]
  have happ0 : ∀ (b : Bool) (x : Qubits W),
      (Fin.append (fun _ : Fin 1 => b) x : Qubits (1 + W)) 0 = b :=
    fun b x => Fin.append_left (fun _ : Fin 1 => b) x 0
  have happt : ∀ (b : Bool) (x : Qubits W) (j : Fin W),
      (Fin.append (fun _ : Fin 1 => b) x : Qubits (1 + W)) (Fin.natAdd 1 j) = x j :=
    fun b x j => Fin.append_right (fun _ : Fin 1 => b) x j
  have hsp : (∑ z : Qubits (1 + W), liftCtrl W A y z *
      (if z 0 = false then u.ofLp (fun j => z (Fin.natAdd 1 j)) else 0)) =
      ∑ p ∈ Finset.univ, liftCtrl W A y ((splitCtrl W).symm p) *
        (if ((splitCtrl W).symm p) 0 = false then
          u.ofLp (fun j => ((splitCtrl W).symm p) (Fin.natAdd 1 j)) else 0) :=
    (Fintype.sum_equiv (splitCtrl W).symm _ _ fun _ => rfl).symm
  rw [hsp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [splitCtrl, Equiv.coe_fn_symm_mk, happ0, happt, Bool.true_eq_false, ↓reduceIte,
    mul_zero, Finset.sum_const_zero, zero_add]
  cases hy0 : y 0
  · rw [if_pos rfl]
    have hl : ∀ x : Qubits W,
        liftCtrl W A y (Fin.append (fun _ : Fin 1 => false) x) =
          if (fun j : Fin W => y (Fin.natAdd 1 j)) = x then 1 else 0 := by
      intro x; rw [liftCtrl_apply]; simp [hy0, splitCtrl, happ0, happt, Matrix.one_apply]
    simp only [hl]
    rw [Finset.sum_eq_single (fun j : Fin W => y (Fin.natAdd 1 j))]
    · simp
    · intro x _ hx; simp [hx.symm]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg (by decide)]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hl : liftCtrl W A y (Fin.append (fun _ : Fin 1 => false) x) = 0 := by
      rw [liftCtrl_apply]; simp [hy0, splitCtrl, happ0]
    rw [hl, zero_mul]

lemma act_liftCtrl_liftBool_true (W : ℕ) (A : Matrix (Qubits W) (Qubits W) ℂ)
    (u : EuclideanSpace ℂ (Qubits W)) :
    act (liftCtrl W A) (liftBool W true u) = liftBool W true (act A u) := by
  apply WithLp.ofLp_injective; funext y
  simp only [act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp, liftBool]
  have happ0 : ∀ (b : Bool) (x : Qubits W),
      (Fin.append (fun _ : Fin 1 => b) x : Qubits (1 + W)) 0 = b :=
    fun b x => Fin.append_left (fun _ : Fin 1 => b) x 0
  have happt : ∀ (b : Bool) (x : Qubits W) (j : Fin W),
      (Fin.append (fun _ : Fin 1 => b) x : Qubits (1 + W)) (Fin.natAdd 1 j) = x j :=
    fun b x j => Fin.append_right (fun _ : Fin 1 => b) x j
  have hsp : (∑ z : Qubits (1 + W), liftCtrl W A y z *
      (if z 0 = true then u.ofLp (fun j => z (Fin.natAdd 1 j)) else 0)) =
      ∑ p ∈ Finset.univ, liftCtrl W A y ((splitCtrl W).symm p) *
        (if ((splitCtrl W).symm p) 0 = true then
          u.ofLp (fun j => ((splitCtrl W).symm p) (Fin.natAdd 1 j)) else 0) :=
    (Fintype.sum_equiv (splitCtrl W).symm _ _ fun _ => rfl).symm
  rw [hsp, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [splitCtrl, Equiv.coe_fn_symm_mk, happ0, happt, Bool.false_eq_true, ↓reduceIte,
    mul_zero, Finset.sum_const_zero, add_zero]
  cases hy0 : y 0
  · rw [if_neg Bool.false_ne_true]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hl : liftCtrl W A y (Fin.append (fun _ : Fin 1 => true) x) = 0 := by
      rw [liftCtrl_apply]; simp [hy0, splitCtrl, happ0]
    rw [hl, zero_mul]
  · rw [if_pos rfl]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hl : liftCtrl W A y (Fin.append (fun _ : Fin 1 => true) x) =
        A (fun j => y (Fin.natAdd 1 j)) x := by
      rw [liftCtrl_apply]; simp [hy0, splitCtrl, happ0, happt]
    rw [hl]

lemma act_x0_padVec0 (W : ℕ) (v : EuclideanSpace ℂ (Qubits (1 + W))) :
    act (circUnitary ([.x ⟨0, by omega⟩] : List (Instr (W + 2)))) (padVec0 W v) =
      padVec0 W (act (circUnitary ([.x ⟨0, by omega⟩] : List (Instr (1 + W)))) v) := by
  have hx : ([.x ⟨0, by omega⟩] : List (Instr (W + 2))) =
      mapCirc (shiftCtrl0Exact W) ([.x ⟨0, by omega⟩] : List (Instr (1 + W))) := by
    simp only [mapCirc, mapInstr, List.map_cons, List.map_nil]
    congr 1
  rw [hx, circUnitary_mapCirc, act_embedOp_shiftCtrl0]

lemma embedVec_padTo_sum_sub {X₀ X₁ : Type} [Fintype X₀] [Fintype X₁] {m₀ m₁ W : ℕ}
    (hm₀ : m₀ ≤ W) (hm₁ : m₁ ≤ W) (c₀ : X₀ → Qubits m₀) (c₁ : X₁ → Qubits m₁)
    (φ : EuclideanSpace ℂ (X₀ ⊕ X₁)) :
    embedVec (fun p => padTo (1 + W) (sumCode c₀ c₁ p)) φ =
      liftBool W false (embedVec (fun x => padTo W (c₀ x)) (WithLp.toLp 2 (fun x => φ.ofLp (.inl x)))) +
      liftBool W true (embedVec (fun x => padTo W (c₁ x)) (WithLp.toLp 2 (fun x => φ.ofLp (.inr x)))) := by
  apply WithLp.ofLp_injective; funext y
  simp only [embedVec, liftBool, PiLp.add_apply, WithLp.ofLp_toLp, Fintype.sum_sum_type]
  have happ0 : ∀ (b : Bool) (u : Qubits (max m₀ m₁)),
      padTo (1 + W) (Fin.append (fun _ : Fin 1 => b) u) 0 = b := by
    intro b u
    simp only [padTo]
    rw [dif_pos (by change (0 : ℕ) < 1 + max m₀ m₁; omega)]
    change (Fin.append (fun _ : Fin 1 => b) u) (Fin.castAdd (max m₀ m₁) 0) = b
    exact Fin.append_left _ _ 0
  have hsub : ∀ (b : Bool) {Z : Type} {m : ℕ} (hm : m ≤ max m₀ m₁) (hW : max m₀ m₁ ≤ W)
      (cz : Z → Qubits m) (z : Z),
      padTo (1 + W) (Fin.append (fun _ : Fin 1 => b) (padTo (max m₀ m₁) (cz z))) = y ↔
        (y 0 = b ∧ padTo W (cz z) = fun j : Fin W => y (Fin.natAdd 1 j)) := by
    intro b Z m hm hW cz z
    constructor
    · intro h
      refine ⟨?_, funext fun j => ?_⟩
      · rw [← h]; exact happ0 b _
      · rw [← h]
        simp only [padTo, Fin.val_natAdd]
        by_cases h1 : 1 + j.val < 1 + max m₀ m₁
        · rw [dif_pos h1]
          have h1' : j.val < max m₀ m₁ := by omega
          have happ_r : (Fin.append (fun _ : Fin 1 => b) (padTo (max m₀ m₁) (cz z)))
              ⟨1 + j.val, h1⟩ = (padTo (max m₀ m₁) (cz z)) ⟨j.val, h1'⟩ :=
            Fin.append_right _ _ ⟨j.val, h1'⟩
          rw [happ_r]
          simp only [padTo]
        · have hjm : ¬ (j.val < m) := by omega
          rw [dif_neg hjm, dif_neg h1]
    · rintro ⟨hy0, htail⟩
      funext a
      refine Fin.addCases (fun c => ?_) (fun j => ?_) a
      · have hc : c = 0 := Subsingleton.elim c 0
        subst hc
        change padTo (1 + W) (Fin.append (fun _ : Fin 1 => b) (padTo (max m₀ m₁) (cz z))) 0 = y 0
        rw [happ0, hy0]
      · have hj := congrFun htail j
        rw [← hj]
        simp only [padTo, Fin.val_natAdd]
        by_cases h1 : 1 + j.val < 1 + max m₀ m₁
        · rw [dif_pos h1]
          have h1' : j.val < max m₀ m₁ := by omega
          have happ_r : (Fin.append (fun _ : Fin 1 => b) (padTo (max m₀ m₁) (cz z)))
              ⟨1 + j.val, h1⟩ = (padTo (max m₀ m₁) (cz z)) ⟨j.val, h1'⟩ :=
            Fin.append_right _ _ ⟨j.val, h1'⟩
          rw [happ_r]
          simp only [padTo]
        · have hjm : ¬ (j.val < m) := by omega
          rw [dif_neg hjm, dif_neg h1]
  have hmaxW : max m₀ m₁ ≤ W := max_le hm₀ hm₁
  have hL : (∑ x : X₀, if padTo (1 + W) (sumCode c₀ c₁ (.inl x)) = y then φ.ofLp (.inl x) else 0) =
      if y 0 = false then
        ∑ x : X₀, if padTo W (c₀ x) = fun j : Fin W => y (Fin.natAdd 1 j) then φ.ofLp (.inl x) else 0
      else 0 := by
    by_cases hy0 : y 0 = false
    · rw [if_pos hy0]
      refine Finset.sum_congr rfl fun x _ => ?_
      change (if padTo (1 + W) (Fin.append (fun _ : Fin 1 => false) (padTo (max m₀ m₁) (c₀ x))) = y
          then φ.ofLp (.inl x) else 0) = _
      have heq := hsub false (le_max_left m₀ m₁) hmaxW c₀ x
      by_cases h1 : padTo (1 + W) (Fin.append (fun _ : Fin 1 => false) (padTo (max m₀ m₁) (c₀ x))) = y
      · rw [if_pos h1, if_pos (heq.mp h1).2]
      · rw [if_neg h1, if_neg (fun ht => h1 (heq.mpr ⟨hy0, ht⟩))]
    · rw [if_neg hy0]
      refine Finset.sum_eq_zero fun x _ => ?_
      change (if padTo (1 + W) (Fin.append (fun _ : Fin 1 => false) (padTo (max m₀ m₁) (c₀ x))) = y
          then φ.ofLp (.inl x) else 0) = 0
      have heq := hsub false (le_max_left m₀ m₁) hmaxW c₀ x
      rw [if_neg (fun h => hy0 (heq.mp h).1)]
  have hR : (∑ x : X₁, if padTo (1 + W) (sumCode c₀ c₁ (.inr x)) = y then φ.ofLp (.inr x) else 0) =
      if y 0 = true then
        ∑ x : X₁, if padTo W (c₁ x) = fun j : Fin W => y (Fin.natAdd 1 j) then φ.ofLp (.inr x) else 0
      else 0 := by
    by_cases hy0 : y 0 = true
    · rw [if_pos hy0]
      refine Finset.sum_congr rfl fun x _ => ?_
      change (if padTo (1 + W) (Fin.append (fun _ : Fin 1 => true) (padTo (max m₀ m₁) (c₁ x))) = y
          then φ.ofLp (.inr x) else 0) = _
      have heq := hsub true (le_max_right m₀ m₁) hmaxW c₁ x
      by_cases h1 : padTo (1 + W) (Fin.append (fun _ : Fin 1 => true) (padTo (max m₀ m₁) (c₁ x))) = y
      · rw [if_pos h1, if_pos (heq.mp h1).2]
      · rw [if_neg h1, if_neg (fun ht => h1 (heq.mpr ⟨hy0, ht⟩))]
    · rw [if_neg hy0]
      refine Finset.sum_eq_zero fun x _ => ?_
      change (if padTo (1 + W) (Fin.append (fun _ : Fin 1 => true) (padTo (max m₀ m₁) (c₁ x))) = y
          then φ.ofLp (.inr x) else 0) = 0
      have heq := hsub true (le_max_right m₀ m₁) hmaxW c₁ x
      rw [if_neg (fun h => hy0 (heq.mp h).1)]
  rw [hL, hR]

lemma embedVec_padTo_sum_two {X₀ X₁ : Type} [Fintype X₀] [Fintype X₁] {m₀ m₁ W : ℕ}
    (hm₀ : m₀ ≤ W) (hm₁ : m₁ ≤ W) (c₀ : X₀ → Qubits m₀) (c₁ : X₁ → Qubits m₁)
    (φ : EuclideanSpace ℂ (X₀ ⊕ X₁)) :
    embedVec (fun p => padTo (W + 2) (sumCode c₀ c₁ p)) φ =
      padVec0 W (embedVec (fun p => padTo (1 + W) (sumCode c₀ c₁ p)) φ) := by
  have hm : 1 + max m₀ m₁ ≤ 1 + W := by have := max_le hm₀ hm₁; omega
  apply WithLp.ofLp_injective; funext y
  simp only [embedVec, padVec0, WithLp.ofLp_toLp]
  by_cases hyanc : y ⟨1 + W, by omega⟩ = false
  · rw [if_pos hyanc]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hiff : padTo (W + 2) (sumCode c₀ c₁ p) = y ↔
        padTo (1 + W) (sumCode c₀ c₁ p) = (fun j : Fin (1 + W) => y ⟨j.val, by omega⟩) := by
      constructor
      · intro h; funext j
        have hj := congrFun h ⟨j.val, by omega⟩
        simpa [padTo] using hj
      · intro h; funext a
        have ha_lt := a.isLt
        by_cases ha : a.val < 1 + W
        · simpa [padTo, ha] using congrFun h ⟨a.val, ha⟩
        · have ha_eq : a = ⟨1 + W, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [ha_eq, hyanc]
          simp [padTo, show ¬ (1 + W < 1 + max m₀ m₁) by omega]
    by_cases h : padTo (W + 2) (sumCode c₀ c₁ p) = y
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  · rw [if_neg hyanc]
    refine Finset.sum_eq_zero fun p _ => ?_
    have hne : padTo (W + 2) (sumCode c₀ c₁ p) ≠ y := by
      intro h; apply hyanc
      have hanc := congrFun h ⟨1 + W, by omega⟩
      have hpad0 : padTo (W + 2) (sumCode c₀ c₁ p) ⟨1 + W, by omega⟩ = false := by
        simp [padTo, show ¬ (1 + W < 1 + max m₀ m₁) by omega]
      rw [← hanc, hpad0]
    rw [if_neg hne]

lemma act_sumCircExact {w₀ w₁ : ℕ} (c₀ : List (Instr w₀)) (c₁ : List (Instr w₁))
    (v₀ v₁ : EuclideanSpace ℂ (Qubits (max w₀ w₁))) :
    act (circUnitary (sumCircExact w₀ w₁ c₀ c₁))
      (padVec0 (max w₀ w₁) (liftBool (max w₀ w₁) false v₀ + liftBool (max w₀ w₁) true v₁)) =
      padVec0 (max w₀ w₁)
        (liftBool (max w₀ w₁) false
            (act (circUnitary (mapCirc (shiftPrefix w₀ (max w₀ w₁) (le_max_left _ _)) c₀)) v₀) +
         liftBool (max w₀ w₁) true
            (act (circUnitary (mapCirc (shiftPrefix w₁ (max w₀ w₁) (le_max_right _ _)) c₁)) v₁)) := by
  unfold sumCircExact
  dsimp only
  rw [circUnitary_append, circUnitary_append, circUnitary_append,
    act_mul, act_mul, act_mul,
    act_x0_padVec0, act_add, act_X0_liftBool, act_X0_liftBool, Bool.not_false, Bool.not_true,
    act_ctrlCircExact_padVec0, act_add, act_liftCtrl_liftBool_true, act_liftCtrl_liftBool_false,
    act_x0_padVec0, act_add, act_X0_liftBool, act_X0_liftBool, Bool.not_false, Bool.not_true,
    act_ctrlCircExact_padVec0, act_add, act_liftCtrl_liftBool_false, act_liftCtrl_liftBool_true]

lemma liftBool_pair_sub (W : ℕ) (a₀ a₁ b₀ b₁ : EuclideanSpace ℂ (Qubits W)) :
    (liftBool W false a₀ + liftBool W true a₁) - (liftBool W false b₀ + liftBool W true b₁) =
      liftBool W false (a₀ - b₀) + liftBool W true (a₁ - b₁) := by
  apply WithLp.ofLp_injective; funext y
  simp only [liftBool, PiLp.sub_apply, PiLp.add_apply, WithLp.ofLp_toLp]
  split_ifs <;> ring

end SumComb

end GL2QFT_Sum_Aux

theorem solution {P : FieldData → Prop} {X₀ X₁ Y₀ Y₁ : FieldData → Type}
    [∀ D, Fintype (X₀ D)] [∀ D, Fintype (X₁ D)] [∀ D, Fintype (Y₀ D)] [∀ D, Fintype (Y₁ D)]
    {m₀ m₁ n₀ n₁ : FieldData → ℕ}
    {cx₀ : ∀ D, X₀ D → Qubits (m₀ D)} {cx₁ : ∀ D, X₁ D → Qubits (m₁ D)}
    {cy₀ : ∀ D, Y₀ D → Qubits (n₀ D)} {cy₁ : ∀ D, Y₁ D → Qubits (n₁ D)}
    {Φ₀ : ∀ D, Matrix (Y₀ D) (X₀ D) ℂ} {Φ₁ : ∀ D, Matrix (Y₁ D) (X₁ D) ℂ}
    (h0 : UniformlyImplementsOn P cx₀ cy₀ Φ₀)
    (h1 : UniformlyImplementsOn P cx₁ cy₁ Φ₁) :
    UniformlyImplementsOn P (fun D => sumCode (cx₀ D) (cx₁ D)) (fun D => sumCode (cy₀ D) (cy₁ D))
      (fun D => sumMat (Φ₀ D) (Φ₁ D)) := by
  obtain ⟨w₀, c₀, f₀, k₀, hf0_poly, hf0_spec, hlen₀, himp₀⟩ := h0
  obtain ⟨w₁, c₁, f₁, k₁, hf1_poly, hf1_spec, hlen₁, himp₁⟩ := h1
  obtain ⟨M₀⟩ := hf0_poly
  obtain ⟨M₁⟩ := hf1_poly
  let fFan := fun s => OAI.MetricKMedian.Binary.encodePair id id (f₀ s, f₁ s)
  let Mfan := GL2QFT_Sum_Aux.TM2Fanout.fanout M₀ M₁
  let Mfull := GL2QFT_Sum_Aux.TM2Comp.comp Mfan GL2QFT_Sum_Aux.sumPostExactProg.stock
  refine ⟨fun D k => max (w₀ D k) (w₁ D k) + 2,
    fun D k => GL2QFT_Sum_Aux.sumCircExact (w₀ D k) (w₁ D k) (c₀ D k) (c₁ D k),
    (GL2QFT_Sum_Aux.sumInnerExact ∘ GL2QFT_Sum_Aux.unpackPairAux none) ∘ fFan,
    k₀ + k₁ + 8,
    ⟨Mfull⟩, ?_, ?_, ?_⟩
  · intro D hD k
    simp only [Function.comp_apply, fFan, OAI.MetricKMedian.Binary.encodePair, id_eq]
    rw [hf0_spec D hD k, hf1_spec D hD k, GL2QFT_Sum_Aux.unpackPairAux_quote,
      GL2QFT_Sum_Aux.sumInnerExact_eq]
  · intro D hD k
    set B := Nat.log 2 D.q + k + 2
    have hB : 2 ≤ B := by omega
    have hB1 : 1 ≤ B := by omega
    have h128 : 128 ≤ B ^ 7 := by
      calc 128 = 2 ^ 7 := by decide
        _ ≤ B ^ 7 := Nat.pow_le_pow_left hB 7
    have hl0 := hlen₀ D hD k
    have hl1 := hlen₁ D hD k
    have hpow0 : B ^ k₀ ≤ B ^ (k₀ + k₁) := Nat.pow_le_pow_right hB1 (by omega)
    have hpow1 : B ^ k₁ ≤ B ^ (k₀ + k₁) := Nat.pow_le_pow_right hB1 (by omega)
    have hsum_len := GL2QFT_Sum_Aux.sumCircExact_length_le (c₀ D k) (c₁ D k)
    have h67 : 2 + 67 * (k₀ * B ^ k₀ + k₁ * B ^ k₁) ≤
        (67 * (k₀ + k₁) + 2) * B ^ (k₀ + k₁) := by
      have hpow0' : k₀ * B ^ k₀ ≤ k₀ * B ^ (k₀ + k₁) := Nat.mul_le_mul_left _ hpow0
      have hpow1' : k₁ * B ^ k₁ ≤ k₁ * B ^ (k₀ + k₁) := Nat.mul_le_mul_left _ hpow1
      have h2 : 2 ≤ 2 * B ^ (k₀ + k₁) := Nat.le_mul_of_pos_right 2 (Nat.pow_pos (by omega))
      nlinarith
    have hcoeff : 67 * (k₀ + k₁) + 2 ≤ 128 * (k₀ + k₁ + 8) := by omega
    have hfinal : (67 * (k₀ + k₁) + 2) * B ^ (k₀ + k₁) ≤
        (k₀ + k₁ + 8) * B ^ (k₀ + k₁ + 8) := by
      calc (67 * (k₀ + k₁) + 2) * B ^ (k₀ + k₁)
          ≤ (128 * (k₀ + k₁ + 8)) * B ^ (k₀ + k₁) := Nat.mul_le_mul_right _ hcoeff
        _ ≤ (B ^ 7 * (k₀ + k₁ + 8)) * B ^ (k₀ + k₁) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h128)
        _ = (k₀ + k₁ + 8) * B ^ (k₀ + k₁ + 7) := by rw [pow_add]; ring
        _ ≤ (k₀ + k₁ + 8) * B ^ (k₀ + k₁ + 8) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB1 (by omega))
    calc (GL2QFT_Sum_Aux.sumCircExact (w₀ D k) (w₁ D k) (c₀ D k) (c₁ D k)).length
        ≤ 2 + 67 * ((c₀ D k).length + (c₁ D k).length) := hsum_len
      _ ≤ 2 + 67 * (k₀ * B ^ k₀ + k₁ * B ^ k₁) := by
          have hl0' : (c₀ D k).length ≤ k₀ * B ^ k₀ := hl0
          have hl1' : (c₁ D k).length ≤ k₁ * B ^ k₁ := hl1
          omega
      _ ≤ (67 * (k₀ + k₁) + 2) * B ^ (k₀ + k₁) := h67
      _ ≤ (k₀ + k₁ + 8) * B ^ (k₀ + k₁ + 8) := hfinal
  · intro D hD k
    obtain ⟨hm₀_w, hn₀_w, himp₀_k⟩ := himp₀ D hD k
    obtain ⟨hm₁_w, hn₁_w, himp₁_k⟩ := himp₁ D hD k
    set W := max (w₀ D k) (w₁ D k)
    have hw₀W : w₀ D k ≤ W := le_max_left _ _
    have hw₁W : w₁ D k ≤ W := le_max_right _ _
    have hm₀W : m₀ D ≤ W := hm₀_w.trans hw₀W
    have hm₁W : m₁ D ≤ W := hm₁_w.trans hw₁W
    have hn₀W : n₀ D ≤ W := hn₀_w.trans hw₀W
    have hn₁W : n₁ D ≤ W := hn₁_w.trans hw₁W
    refine ⟨by change 1 + max (m₀ D) (m₁ D) ≤ W + 2; have := max_le hm₀W hm₁W; omega,
      by change 1 + max (n₀ D) (n₁ D) ≤ W + 2; have := max_le hn₀W hn₁W; omega, ?_⟩
    intro ψ
    let ψ₀ : EuclideanSpace ℂ (X₀ D) := WithLp.toLp 2 (fun x => ψ.ofLp (.inl x))
    let ψ₁ : EuclideanSpace ℂ (X₁ D) := WithLp.toLp 2 (fun x => ψ.ofLp (.inr x))
    have hnormψ : ‖ψ₀‖ ^ 2 + ‖ψ₁‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_sum_type]
    have hemb_in := GL2QFT_Sum_Aux.embedVec_padTo_sum_two hm₀W hm₁W (cx₀ D) (cx₁ D) ψ
    have hemb_in_sub := GL2QFT_Sum_Aux.embedVec_padTo_sum_sub hm₀W hm₁W (cx₀ D) (cx₁ D) ψ
    have hemb_out := GL2QFT_Sum_Aux.embedVec_padTo_sum_two hn₀W hn₁W (cy₀ D) (cy₁ D)
      (WithLp.toLp 2 ((sumMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp))
    have hemb_out_sub := GL2QFT_Sum_Aux.embedVec_padTo_sum_sub hn₀W hn₁W (cy₀ D) (cy₁ D)
      (WithLp.toLp 2 ((sumMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp))
    have hmul_inl : (WithLp.toLp 2 (fun y =>
        (WithLp.toLp 2 ((sumMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp)).ofLp (.inl y)) :
        EuclideanSpace ℂ (Y₀ D)) = WithLp.toLp 2 ((Φ₀ D).mulVec ψ₀.ofLp) := by
      apply WithLp.ofLp_injective; funext y
      simp only [Matrix.mulVec, dotProduct, sumMat, Matrix.of_apply, Fintype.sum_sum_type,
        WithLp.ofLp_toLp, ψ₀, zero_mul, Finset.sum_const_zero, add_zero]
    have hmul_inr : (WithLp.toLp 2 (fun y =>
        (WithLp.toLp 2 ((sumMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp)).ofLp (.inr y)) :
        EuclideanSpace ℂ (Y₁ D)) = WithLp.toLp 2 ((Φ₁ D).mulVec ψ₁.ofLp) := by
      apply WithLp.ofLp_injective; funext y
      simp only [Matrix.mulVec, dotProduct, sumMat, Matrix.of_apply, Fintype.sum_sum_type,
        WithLp.ofLp_toLp, ψ₁, zero_mul, Finset.sum_const_zero, zero_add]
    rw [hmul_inl, hmul_inr] at hemb_out_sub
    let c₀' := mapCirc (GL2QFT_Sum_Aux.shiftPrefix (w₀ D k) W hw₀W) (c₀ D k)
    let c₁' := mapCirc (GL2QFT_Sum_Aux.shiftPrefix (w₁ D k) W hw₁W) (c₁ D k)
    let U₀ := circUnitary c₀'
    let U₁ := circUnitary c₁'
    let v₀ := embedVec (fun x => padTo W (cx₀ D x)) ψ₀
    let v₁ := embedVec (fun x => padTo W (cx₁ D x)) ψ₁
    let id₀ := embedVec (fun y => padTo W (cy₀ D y)) (WithLp.toLp 2 ((Φ₀ D).mulVec ψ₀.ofLp))
    let id₁ := embedVec (fun y => padTo W (cy₁ D y)) (WithLp.toLp 2 ((Φ₁ D).mulVec ψ₁.ofLp))
    have htrace : act (circUnitary (GL2QFT_Sum_Aux.sumCircExact (w₀ D k) (w₁ D k) (c₀ D k) (c₁ D k)))
        (embedVec (fun p => padTo (W + 2) (sumCode (cx₀ D) (cx₁ D) p)) ψ) =
        GL2QFT_Sum_Aux.padVec0 W
          (GL2QFT_Sum_Aux.liftBool W false (act U₀ v₀) +
           GL2QFT_Sum_Aux.liftBool W true (act U₁ v₁)) := by
      rw [hemb_in, hemb_in_sub]
      exact GL2QFT_Sum_Aux.act_sumCircExact (c₀ D k) (c₁ D k) v₀ v₁
    rw [htrace, hemb_out, hemb_out_sub, ← GL2QFT_Sum_Aux.padVec0_sub,
      GL2QFT_Sum_Aux.padVec0_norm, GL2QFT_Sum_Aux.liftBool_pair_sub]
    have herr₀ : ‖act U₀ v₀ - id₀‖ ≤ (1 / 2 : ℝ) ^ k * ‖ψ₀‖ :=
      GL2QFT_Sum_Aux.padCirc_implements hm₀_w hn₀_w hw₀W (cx₀ D) (cy₀ D) (c₀ D k) (Φ₀ D)
        ((1 / 2 : ℝ) ^ k) himp₀_k ψ₀
    have herr₁ : ‖act U₁ v₁ - id₁‖ ≤ (1 / 2 : ℝ) ^ k * ‖ψ₁‖ :=
      GL2QFT_Sum_Aux.padCirc_implements hm₁_w hn₁_w hw₁W (cx₁ D) (cy₁ D) (c₁ D k) (Φ₁ D)
        ((1 / 2 : ℝ) ^ k) himp₁_k ψ₁
    have hsq : ‖GL2QFT_Sum_Aux.liftBool W false (act U₀ v₀ - id₀) +
        GL2QFT_Sum_Aux.liftBool W true (act U₁ v₁ - id₁)‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ k * ‖ψ‖) ^ 2 := by
      rw [GL2QFT_Sum_Aux.liftBool_norm_sq]
      have h0sq : ‖act U₀ v₀ - id₀‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ k * ‖ψ₀‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mpr herr₀
      have h1sq : ‖act U₁ v₁ - id₁‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ k * ‖ψ₁‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mpr herr₁
      calc ‖act U₀ v₀ - id₀‖ ^ 2 + ‖act U₁ v₁ - id₁‖ ^ 2
          ≤ ((1 / 2 : ℝ) ^ k * ‖ψ₀‖) ^ 2 + ((1 / 2 : ℝ) ^ k * ‖ψ₁‖) ^ 2 := add_le_add h0sq h1sq
        _ = ((1 / 2 : ℝ) ^ k) ^ 2 * (‖ψ₀‖ ^ 2 + ‖ψ₁‖ ^ 2) := by ring
        _ = ((1 / 2 : ℝ) ^ k) ^ 2 * ‖ψ‖ ^ 2 := by rw [hnormψ]
        _ = ((1 / 2 : ℝ) ^ k * ‖ψ‖) ^ 2 := by ring
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp hsq
