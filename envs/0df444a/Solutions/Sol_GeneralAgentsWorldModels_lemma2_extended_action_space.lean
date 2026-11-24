-- Prove2me | solution 1 for GeneralAgentsWorldModels.lemma2_extended_action_space
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:49:15.017135+00:00
-- url     : https://prove2.me/submissions/8b3f0ab5-62f4-4a78-904a-919994473b35

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

set_option autoImplicit false

universe u v

namespace GeneralAgentsWorldModels

section
variable {S A : Type*} [Fintype S]
set_option linter.unusedSectionVars false

private lemma ex_sum_succ {β : Type*} [AddCommMonoid β] (n : ℕ) (F : List S → β) :
    ∑ ss : Fin (n+1) → S, F (List.ofFn ss) = ∑ s1 : S, ∑ ss : Fin n → S, F (s1 :: List.ofFn ss) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => S)).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv, List.ofFn_succ]

private lemma ex_prefix_cons (π : Policy S A) : ∀ (ss : List S) (h : List (S × A)) (s : S),
    ∃ r, pathPrefix π h s ss = h ++ (s, π h s) :: r
  | [], h, s => ⟨[], rfl⟩
  | s' :: ss, h, s => by
    obtain ⟨r, hr⟩ := ex_prefix_cons π ss (h ++ [(s, π h s)]) s'
    exact ⟨(s', π (h ++ [(s, π h s)]) s') :: r, by rw [pathPrefix, hr]; simp⟩

private lemma ex_prefix_length (π : Policy S A) : ∀ (ss : List S) (h : List (S × A)) (s : S),
    (pathPrefix π h s ss).length = h.length + ss.length + 1
  | [], h, s => by simp [pathPrefix]
  | s' :: ss, h, s => by
    rw [pathPrefix, ex_prefix_length π ss]; simp; omega

private lemma ex_take_prefix (π : Policy S A) (ss : List S) (h : List (S × A)) (s : S) :
    (pathPrefix π h s ss).take (h.length + 1) = h ++ [(s, π h s)] := by
  obtain ⟨r, hr⟩ := ex_prefix_cons π ss h s
  rw [hr]; simp [List.take_append]

private lemma ex_pw_nonneg (M : CMP S A) (π : Policy S A) : ∀ (ss : List S) (h : List (S × A))
    (s : S), 0 ≤ pathWeight M π h s ss
  | [], h, s => by simp [pathWeight]
  | s' :: ss, h, s => by
    rw [pathWeight]; exact mul_nonneg (M.nonneg _ _ _) (ex_pw_nonneg M π ss _ _)

private lemma ex_sum_one (M : CMP S A) (π : Policy S A) : ∀ (k : ℕ) (h : List (S × A)) (s : S),
    ∑ ss : Fin k → S, pathWeight M π h s (List.ofFn ss) = 1
  | 0, h, s => by simp [pathWeight]
  | k+1, h, s => by
    rw [ex_sum_succ]
    simp only [pathWeight, ← Finset.mul_sum, ex_sum_one M π k, mul_one]
    exact M.sum_one s (π h s)

private lemma ex_split (M : CMP S A) (π : Policy S A) (f : List (S × A) → ℝ) (k : ℕ) :
    ∀ (T : ℕ) (h : List (S × A)) (s : S),
    ∑ ss : Fin (k + T) → S, pathWeight M π h s (List.ofFn ss) *
        f ((pathPrefix π h s (List.ofFn ss)).take (h.length + T + 1)) =
      ∑ ss : Fin T → S, pathWeight M π h s (List.ofFn ss) * f (pathPrefix π h s (List.ofFn ss))
  | 0, h, s => by
    simp only [Nat.add_zero, ex_take_prefix]
    rw [← Finset.sum_mul, ex_sum_one]
    simp [pathWeight, pathPrefix]
  | T+1, h, s => by
    have e : h.length + (T + 1) + 1 = (h ++ [(s, π h s)]).length + T + 1 := by simp; omega
    show ∑ ss : Fin (k + T + 1) → S, _ = _
    rw [ex_sum_succ (k + T) (fun L => pathWeight M π h s L *
      f ((pathPrefix π h s L).take (h.length + (T + 1) + 1))),
      ex_sum_succ T (fun L => pathWeight M π h s L * f (pathPrefix π h s L)), e]
    simp only [pathWeight, pathPrefix, mul_assoc, ← Finset.mul_sum]
    refine Finset.sum_congr rfl fun s1 _ => ?_
    rw [ex_split M π f k T]

private lemma ex_dec_take {ψ : CompGoal S A} {P : List (S × A)} (n : ℕ)
    (hd : Decides ψ (P.take n)) : Decides ψ P := by
  intro τ hτ
  apply hd τ
  intro i hi
  rw [List.getElem_take]
  exact hτ i (by simp at hi; omega)

open Classical in
private lemma ex_upTo_mono (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (k T : ℕ) : succProbUpTo M ψ π s₀ T ≤ succProbUpTo M ψ π s₀ (k + T) := by
  unfold succProbUpTo
  rw [← ex_split M π (fun L => if Decides ψ L then 1 else 0) k T [] s₀]
  apply Finset.sum_le_sum
  intro ss _
  apply mul_le_mul_of_nonneg_left _ (ex_pw_nonneg _ _ _ _ _)
  by_cases h1 : Decides ψ ((pathPrefix π [] s₀ (List.ofFn ss)).take
      (([] : List (S × A)).length + T + 1))
  · rw [if_pos h1, if_pos (ex_dec_take _ h1)]
  · rw [if_neg h1]; split_ifs <;> norm_num

private lemma ex_upTo_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (T : ℕ) : succProbUpTo M ψ π s₀ T ≤ 1 := by
  unfold succProbUpTo
  refine le_trans (Finset.sum_le_sum fun ss _ => ?_) (ex_sum_one M π T [] s₀).le
  have := ex_pw_nonneg M π (List.ofFn ss) [] s₀
  split_ifs <;> nlinarith

private lemma ex_upTo_nonneg (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (T : ℕ) : 0 ≤ succProbUpTo M ψ π s₀ T := by
  unfold succProbUpTo
  apply Finset.sum_nonneg
  intro ss _
  have := ex_pw_nonneg M π (List.ofFn ss) [] s₀
  split_ifs <;> nlinarith

private lemma ex_le_succProb (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S)
    (T : ℕ) : succProbUpTo M ψ π s₀ T ≤ succProb M ψ π s₀ :=
  le_ciSup ⟨1, by rintro _ ⟨T, rfl⟩; exact ex_upTo_le_one M ψ π s₀ T⟩ T

private lemma ex_succProb_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S) :
    succProb M ψ π s₀ ≤ 1 :=
  ciSup_le fun T => ex_upTo_le_one M ψ π s₀ T

private lemma ex_le_optProb (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S) :
    succProb M ψ π s₀ ≤ optProb M ψ s₀ :=
  le_ciSup (f := fun π => succProb M ψ π s₀)
    ⟨1, by rintro _ ⟨π, rfl⟩; exact ex_succProb_le_one M ψ π s₀⟩ π


end

section
variable {S A : Type*} [Fintype S]
set_option linter.unusedSectionVars false

private def ex_liftL (h : List (S × A)) : List (S × Option A) := h.map fun x => (x.1, some x.2)

private def ex_unliftL (a0 : A) (h : List (S × Option A)) : List (S × A) :=
  h.map fun x => (x.1, x.2.getD a0)

private def ex_liftPol (a0 : A) (π : Policy S A) : Policy S (Option A) :=
  fun h s => some (π (ex_unliftL a0 h) s)

private lemma ex_unlift_lift (a0 : A) (h : List (S × A)) : ex_unliftL a0 (ex_liftL h) = h := by
  induction h with
  | nil => rfl
  | cons x t ih => simp only [ex_unliftL, ex_liftL] at ih ⊢; simp [ih]

private lemma ex_liftPol_lift (a0 : A) (π : Policy S A) (h : List (S × A)) (s : S) :
    ex_liftPol a0 π (ex_liftL h) s = some (π h s) := by
  simp [ex_liftPol, ex_unlift_lift]

private lemma ex_pw_lift (M : CMP S A) (M' : CMP S (Option A))
    (hM' : ∀ s a s', M'.P s (some a) s' = M.P s a s') (a0 : A) (π : Policy S A) :
    ∀ (ss : List S) (h : List (S × A)) (s : S),
      pathWeight M' (ex_liftPol a0 π) (ex_liftL h) s ss = pathWeight M π h s ss
  | [], h, s => rfl
  | s' :: ss, h, s => by
    simp only [pathWeight, ex_liftPol_lift, hM']
    rw [show ex_liftL h ++ [(s, some (π h s))] = ex_liftL (h ++ [(s, π h s)]) by
      simp [ex_liftL], ex_pw_lift M M' hM' a0 π ss]

private lemma ex_pp_lift (a0 : A) (π : Policy S A) :
    ∀ (ss : List S) (h : List (S × A)) (s : S),
      pathPrefix (ex_liftPol a0 π) (ex_liftL h) s ss = ex_liftL (pathPrefix π h s ss)
  | [], h, s => by rw [pathPrefix, pathPrefix, ex_liftPol_lift]; simp [ex_liftL]
  | s' :: ss, h, s => by
    simp only [pathPrefix, ex_liftPol_lift]
    rw [show ex_liftL h ++ [(s, some (π h s))] = ex_liftL (h ++ [(s, π h s)]) by
      simp [ex_liftL], ex_pp_lift a0 π ss]

private lemma ex_mem_lift (g : Set (S × A)) (y : S × A) :
    (y.1, some y.2) ∈ (fun x : S × A => (x.1, some x.2)) '' g ↔ y ∈ g := by
  constructor
  · rintro ⟨x, hx, he⟩
    have : x = y := by
      simp only [Prod.mk.injEq, Option.some.injEq] at he
      exact Prod.ext he.1 he.2
    exact this ▸ hx
  · intro hy; exact ⟨y, hy, rfl⟩

/-- Satisfaction of a sequential goal is witnessed by a finite prefix, and survives lifting. -/
private lemma ex_seq_lift (τ : ℕ → S × A) : ∀ (φ : SeqGoal S A) (t : ℕ), seqSat τ φ t →
    ∃ N, ∀ τ' : ℕ → S × Option A, (∀ i < N, τ' i = ((τ i).1, some (τ i).2)) →
      seqSat τ' (φ.map fun sg => ⟨sg.op, (fun x : S × A => (x.1, some x.2)) '' sg.g⟩) t
  | [], t, _ => ⟨0, fun τ' _ => by simp [seqSat]⟩
  | sg :: rest, t, h => by
    rw [seqSat] at h
    simp only [List.map_cons, seqSat]
    split_ifs at h ⊢ with h1 h2
    · obtain ⟨N, hN⟩ := ex_seq_lift τ rest t h.2
      refine ⟨max N (t + 1), fun τ' hτ' => ⟨?_, hN τ' fun i hi => hτ' i (by omega)⟩⟩
      rw [hτ' t (by omega), ex_mem_lift]; exact h.1
    · obtain ⟨N, hN⟩ := ex_seq_lift τ rest (t + 1) h.2
      refine ⟨max N (t + 2), fun τ' hτ' => ⟨?_, hN τ' fun i hi => hτ' i (by omega)⟩⟩
      rw [hτ' (t + 1) (by omega), ex_mem_lift]; exact h.1
    · obtain ⟨u, htu, hv, hu, hr⟩ := h
      obtain ⟨N, hN⟩ := ex_seq_lift τ rest u hr
      refine ⟨max N (u + 1), fun τ' hτ' => ⟨u, htu, fun v hv1 hv2 => ?_, ?_,
        hN τ' fun i hi => hτ' i (by omega)⟩⟩
      · rw [hτ' v (by omega), ex_mem_lift]; exact hv v hv1 hv2
      · rw [hτ' u (by omega), ex_mem_lift]; exact hu

private lemma ex_comp_lift (ψ : CompGoal S A) (τ : ℕ → S × A) (h : compSat ψ τ) :
    ∃ N, ∀ τ' : ℕ → S × Option A, (∀ i < N, τ' i = ((τ i).1, some (τ i).2)) →
      compSat (liftGoal ψ) τ' := by
  obtain ⟨φ, hφ, hs⟩ := h
  obtain ⟨N, hN⟩ := ex_seq_lift τ φ 0 hs
  exact ⟨N, fun τ' hτ' => ⟨_, List.mem_map_of_mem hφ, hN τ' hτ'⟩⟩

/-- Compactness: a prefix of length `T + 1` that decides `ψ` decides the lifted goal, for the
lifted trajectory, after a uniform number `N` of steps. -/
private lemma ex_uniform [Finite A] (ψ : CompGoal S A) (T : ℕ) : ∃ N, ∀ τ : ℕ → S × A,
    Decides ψ (List.ofFn fun i : Fin (T + 1) => τ i) →
    ∀ τ' : ℕ → S × Option A, (∀ i < N, τ' i = ((τ i).1, some (τ i).2)) →
      compSat (liftGoal ψ) τ' := by
  let _ : TopologicalSpace (S × A) := ⊥
  have : DiscreteTopology (S × A) := ⟨rfl⟩
  have hr : ∀ n, Continuous (fun (τ : ℕ → S × A) (i : Fin n) => τ i) :=
    fun n => continuous_pi fun i => continuous_apply _
  let K : Set (ℕ → S × A) := (fun (τ : ℕ → S × A) (i : Fin (T + 1)) => τ i) ⁻¹'
    {f | Decides ψ (List.ofFn f)}
  have hK : IsCompact K := ((isClosed_discrete _).preimage (hr (T + 1))).isCompact
  let U : ℕ → Set (ℕ → S × A) := fun N => (fun (τ : ℕ → S × A) (i : Fin N) => τ i) ⁻¹'
    {f | ∀ τ' : ℕ → S × Option A, (∀ i : Fin N, τ' i = ((f i).1, some (f i).2)) →
      compSat (liftGoal ψ) τ'}
  have hUo : ∀ N, IsOpen (U N) := fun N => (isOpen_discrete _).preimage (hr N)
  have hmono : Monotone U := by
    intro N N' hNN' τ hτ τ' hτ'
    exact hτ τ' fun i => hτ' ⟨i, lt_of_lt_of_le i.2 hNN'⟩
  have hcov : K ⊆ ⋃ N, U N := by
    intro τ hτ
    have hsat : compSat ψ τ := hτ τ fun i hi => by rw [List.getElem_ofFn]
    obtain ⟨N, hN⟩ := ex_comp_lift ψ τ hsat
    exact Set.mem_iUnion.2 ⟨N, fun τ' hτ' => hN τ' fun i hi => hτ' ⟨i, hi⟩⟩
  obtain ⟨N, hN⟩ := hK.elim_directed_cover U hUo hcov hmono.directed_le
  exact ⟨N, fun τ hτ τ' hτ' => hN hτ τ' fun i => hτ' i i.2⟩

end
end GeneralAgentsWorldModels

open GeneralAgentsWorldModels in
theorem solution {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (M' : CMP S (Option A))
    (hM' : ∀ s a s', M'.P s (some a) s' = M.P s a s') (ψ : CompGoal S A) (s₀ : S) :
    optProb M ψ s₀ ≤ optProb M' (liftGoal ψ) s₀ := by
  classical
  have hA : Nonempty A := Fintype.card_pos_iff.1 (by have := hM.2; omega)
  let a0 : A := Classical.arbitrary A
  apply ciSup_le
  intro π
  refine le_trans ?_ (ex_le_optProb M' _ (ex_liftPol a0 π) s₀)
  apply ciSup_le
  intro T
  obtain ⟨N, hN⟩ := ex_uniform ψ T
  refine le_trans ?_ (ex_le_succProb M' _ _ s₀ (N + T))
  unfold succProbUpTo
  rw [← ex_split M π (fun L => if Decides ψ L then 1 else 0) N T [] s₀]
  apply Finset.sum_le_sum
  intro ss _
  have hw := ex_pw_lift M M' hM' a0 π (List.ofFn ss) [] s₀
  have hp := ex_pp_lift a0 π (List.ofFn ss) [] s₀
  simp only [ex_liftL, List.map_nil] at hw hp
  rw [hw, hp]
  apply mul_le_mul_of_nonneg_left _ (ex_pw_nonneg _ _ _ _ _)
  set P := pathPrefix π [] s₀ (List.ofFn ss) with hPdef
  have hl : P.length = N + T + 1 := by
    rw [hPdef, ex_prefix_length]; simp
  by_cases hd : Decides ψ (P.take (([] : List (S × A)).length + T + 1))
  · rw [if_pos hd, if_pos]
    intro τ' hτ'
    let τ : ℕ → S × A := fun i => if h : i < P.length then P[i] else (s₀, a0)
    apply hN τ _ τ'
    · intro i hi
      have hiP : i < P.length := by omega
      rw [hτ' i (by simp; omega)]
      simp [τ, hiP]
    · convert hd using 1
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp only [List.length_ofFn] at h1
        rw [List.getElem_ofFn, List.getElem_take]
        simp only [τ]; rw [dif_pos (by omega)]
  · rw [if_neg hd]; split_ifs <;> norm_num
