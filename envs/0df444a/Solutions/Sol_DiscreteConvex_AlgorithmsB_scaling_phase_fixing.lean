-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsB.scaling_phase_fixing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:08:11.429997+00:00
-- url     : https://prove2.me/submissions/f2388569-7065-49be-b14d-9396812c2c06

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_AphiActive
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsDeltaFeasibleFlow
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoActiveTriples
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoArcsLeaving
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrecedesIn
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNegR
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPosR
import Definitions.Def_DiscreteConvex_AlgorithmsB_ZVec
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExtremeBaseVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open DiscreteConvex.AlgorithmsB

namespace IFFLib

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The elements of `X` whose position in `L` is below `k`. -/
def Xk (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) : Finset V :=
  X.filter (fun v => ((L v : ℕ)) < k)

theorem Xk_succ (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    Xk L X (k + 1) = Xk L X k ∪ X.filter (fun v => ((L v : ℕ)) = k) := by
  ext v; simp only [Xk, Finset.mem_union, Finset.mem_filter]; constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩

theorem Xk_disj (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    Disjoint (Xk L X k) (X.filter (fun v => ((L v : ℕ)) = k)) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  simp only [Xk, Finset.mem_filter] at h1 h2
  have := h1.2; have := h2.2; omega

theorem Xk_full (L : V ≃ Fin (Fintype.card V)) (X : Finset V) : Xk L X (Fintype.card V) = X := by
  ext v; simp only [Xk, Finset.mem_filter, and_iff_left_iff_imp]; intro _; exact (L v).isLt

theorem Xk_zero (L : V ≃ Fin (Fintype.card V)) (X : Finset V) : Xk L X 0 = ∅ := by
  ext v; simp [Xk]

/-- At most one element of `X` sits at position `k`. -/
theorem filter_eq_k (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    X.filter (fun v => ((L v : ℕ)) = k) = ∅ ∨
      ∃ v ∈ X, ((L v : ℕ)) = k ∧ X.filter (fun v => ((L v : ℕ)) = k) = {v} := by
  by_cases h : ∃ v ∈ X, ((L v : ℕ)) = k
  · obtain ⟨v, hv, hk⟩ := h
    right
    refine ⟨v, hv, hk, ?_⟩
    ext w; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
    · rintro ⟨_, hw⟩
      exact L.injective (Fin.ext (by omega))
    · rintro rfl; exact ⟨hv, hk⟩
  · left
    ext w; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hw hk; exact h ⟨w, hw, hk⟩

theorem prefixUpTo_inter (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (v : V) :
    PrefixUpTo L v ∩ X = Xk L X ((L v : ℕ) + 1) := by
  ext w; simp only [PrefixUpTo, Xk, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.le_def]; constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem prefixBefore_inter (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (v : V) :
    PrefixBefore L v ∩ X = Xk L X ((L v : ℕ)) := by
  ext w; simp only [PrefixBefore, Xk, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.lt_def]; constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- Telescoping along `L`, restricted to `X`. -/
theorem telescope (rho : Finset V → ℤ) (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    ∑ v ∈ Xk L X k, (rho (PrefixUpTo L v ∩ X) - rho (PrefixBefore L v ∩ X)) =
      rho (Xk L X k) - rho ∅ := by
  induction k with
  | zero => simp [Xk_zero]
  | succ k ih =>
    rw [Xk_succ, Finset.sum_union (Xk_disj L X k), ih]
    rcases filter_eq_k L X k with h | ⟨v, hv, hk, h⟩
    · rw [h]; simp
    · rw [h, Finset.sum_singleton, prefixUpTo_inter, prefixBefore_inter, hk, Xk_succ, h]
      ring

theorem telescope_full (rho : Finset V → ℤ) (L : V ≃ Fin (Fintype.card V)) (X : Finset V) :
    ∑ v ∈ X, (rho (PrefixUpTo L v ∩ X) - rho (PrefixBefore L v ∩ X)) = rho X - rho ∅ := by
  have := telescope rho L X (Fintype.card V)
  rwa [Xk_full] at this

/-- On a prefix `W` of `L`, the extreme base sums to `ρ(W)`. -/
theorem extreme_prefix (rho : Finset V → ℤ) (hrho : Submodular rho) (L : V ≃ Fin (Fintype.card V))
    (W : Finset V) (hW : ∀ u ∈ W, ∀ w, L w < L u → w ∈ W) :
    ∑ v ∈ W, ExtremeBaseVec rho L v = rho W := by
  have h := telescope_full rho L W
  rw [hrho.1, sub_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have e1 : PrefixUpTo L v ∩ W = PrefixUpTo L v := by
    ext w; simp only [Finset.mem_inter, PrefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, ?_⟩
      rcases lt_or_eq_of_le h with h' | h'
      · exact hW v hv w h'
      · rw [L.injective h']; exact hv
  have e2 : PrefixBefore L v ∩ W = PrefixBefore L v := by
    ext w; simp only [Finset.mem_inter, PrefixBefore, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, hW v hv w h⟩⟩
  rw [ExtremeBaseVec, e1, e2]

/-- Greedy inequality: the extreme base lies in `B(ρ)`. -/
theorem extreme_le (rho : Finset V → ℤ) (hrho : Submodular rho) (L : V ≃ Fin (Fintype.card V))
    (X : Finset V) : ∑ v ∈ X, ExtremeBaseVec rho L v ≤ rho X := by
  have h := telescope_full rho L X
  rw [hrho.1, sub_zero] at h
  rw [← h]
  refine Finset.sum_le_sum (fun v hv => ?_)
  unfold ExtremeBaseVec
  set A := PrefixBefore L v ∩ X
  set B := PrefixBefore L v
  have hAB : A ⊆ B := Finset.inter_subset_left
  have hvB : v ∉ B := by simp [B, PrefixBefore]
  have e1 : PrefixUpTo L v = insert v B := by
    ext w; simp only [PrefixUpTo, B, PrefixBefore, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h' | h'
      · right; exact h'
      · left; exact L.injective h'
    · rintro (rfl | h); · exact le_rfl
      · exact le_of_lt h
  have e2 : PrefixUpTo L v ∩ X = insert v A := by
    rw [e1]; ext w; simp only [Finset.mem_inter, Finset.mem_insert, A]; constructor
    · rintro ⟨rfl | h, hx⟩; · left; rfl
      · right; exact ⟨h, hx⟩
    · rintro (rfl | ⟨h, hx⟩); · exact ⟨Or.inl rfl, hv⟩
      · exact ⟨Or.inr h, hx⟩
  rw [e2, e1]
  have hsub := hrho.2 (insert v A) B
  have hu : insert v A ∪ B = insert v B := by
    ext w; simp only [Finset.mem_union, Finset.mem_insert]; constructor
    · rintro ((rfl | h) | h); · left; rfl
      · right; exact hAB h
      · right; exact h
    · rintro (rfl | h); · left; left; rfl
      · right; exact h
  have hi : insert v A ∩ B = A := by
    ext w; simp only [Finset.mem_inter, Finset.mem_insert]; constructor
    · rintro ⟨rfl | h, hb⟩; · exact absurd hb hvB
      · exact h
    · intro h; exact ⟨Or.inr h, hAB h⟩
  rw [hu, hi] at hsub
  linarith

variable {ι : Type*} [DecidableEq ι]

theorem x_sum (rho : Finset V → ℤ) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V)))
    (lam : ι → ℝ) (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (X : Finset V) :
    ∑ v ∈ X, x v = ∑ i ∈ I, lam i * ((∑ v ∈ X, ExtremeBaseVec rho (L i) v : ℤ) : ℝ) := by
  rw [Finset.sum_congr rfl (fun v _ => hx.2.2 v), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  rw [Finset.mul_sum]

/-- `x ∈ B(ρ)`: `x(X) ≤ ρ(X)`. -/
theorem x_le (rho : Finset V → ℤ) (hrho : Submodular rho) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ)
    (hx : IsConvexCombOfExtremeBases rho I L lam x) (X : Finset V) :
    ∑ v ∈ X, x v ≤ (rho X : ℝ) := by
  rw [x_sum rho I L lam x hx X]
  calc ∑ i ∈ I, lam i * ((∑ v ∈ X, ExtremeBaseVec rho (L i) v : ℤ) : ℝ)
      ≤ ∑ i ∈ I, lam i * (rho X : ℝ) := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast extreme_le rho hrho (L i) X) (hx.1 i hi))
    _ = (rho X : ℝ) := by rw [← Finset.sum_mul, hx.2.1, one_mul]

/-- On a common prefix, `x(W) = ρ(W)`. -/
theorem x_prefix (rho : Finset V → ℤ) (hrho : Submodular rho) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ)
    (hx : IsConvexCombOfExtremeBases rho I L lam x) (W : Finset V)
    (hW : ∀ i ∈ I, ∀ u ∈ W, ∀ w, L i w < L i u → w ∈ W) :
    ∑ v ∈ W, x v = (rho W : ℝ) := by
  rw [x_sum rho I L lam x hx W]
  calc ∑ i ∈ I, lam i * ((∑ v ∈ W, ExtremeBaseVec rho (L i) v : ℤ) : ℝ)
      = ∑ i ∈ I, lam i * (rho W : ℝ) := Finset.sum_congr rfl (fun i hi => by
        rw [extreme_prefix rho hrho (L i) W (hW i hi)])
    _ = (rho W : ℝ) := by rw [← Finset.sum_mul, hx.2.1, one_mul]

/-- `x⁻(V) ≤ x(X)` for every `X`. -/
theorem neg_le (x : V → ℝ) (X : Finset V) : ∑ v, NegPart x v ≤ ∑ v ∈ X, x v := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ X)]
  have h1 : ∑ v ∈ Finset.univ.filter (· ∈ X), NegPart x v ≤ ∑ v ∈ X, x v := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_le_sum (fun v _ => min_le_right _ _)
  have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬ v ∈ X), NegPart x v ≤ 0 :=
    Finset.sum_nonpos (fun v _ => min_le_left _ _)
  linarith

theorem neg_le_rho (rho : Finset V → ℤ) (hrho : Submodular rho) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ)
    (hx : IsConvexCombOfExtremeBases rho I L lam x) :
    ∑ v, NegPart x v ≤ (MinRho rho : ℝ) := by
  obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Finset V)))
    ⟨∅, Finset.mem_univ _⟩ rho
  unfold MinRho; rw [hX]
  exact (neg_le x X).trans (x_le rho hrho I L lam x hx X)

/-- No active triple: `W` is a prefix of every ordering in `I`. -/
theorem prefix_of_no_active (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (W : Finset V)
    (h : NoActiveTriples I L W) : ∀ i ∈ I, ∀ u ∈ W, ∀ w, L i w < L i u → w ∈ W := by
  intro i hi
  suffices H : ∀ n : ℕ, ∀ u ∈ W, ((L i u : ℕ)) = n → ∀ w, L i w < L i u → w ∈ W by
    intro u hu w hw; exact H _ u hu rfl w hw
  intro n
  induction n with
  | zero => intro u _ hu w hw; rw [Fin.lt_def] at hw; omega
  | succ n ih =>
    intro u hu hun w hw
    have hn : n < Fintype.card V := by have := (L i u).isLt; omega
    set v := (L i).symm ⟨n, hn⟩ with hv
    have hLv : ((L i v : ℕ)) = n := by simp [v]
    have hvW : v ∈ W := by
      by_contra hvW
      exact h i u v ⟨hi, hu, hvW, by unfold ImmediatePred; omega⟩
    rw [Fin.lt_def] at hw
    rcases lt_or_eq_of_le (show ((L i w : ℕ)) ≤ n by omega) with h' | h'
    · exact ih v hvW hLv w (by rw [Fin.lt_def]; omega)
    · have : w = v := (L i).injective (Fin.ext (by omega))
      rw [this]; exact hvW

end IFFLib

namespace IFFFlow

open IFFLib

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem diag_zero (delta : ℝ) (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (v : V) :
    phi v v = 0 := by
  rcases (hphi v v).2.2 with h | h <;> exact h

/-- No active arc leaves `W`, so the net flow out of `W` is nonnegative. -/
theorem bdy_nonneg (delta : ℝ) (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi)
    (W : Finset V) (hno : NoArcsLeaving (AphiActive phi) W) :
    0 ≤ ∑ v ∈ W, FlowBoundary phi v := by
  unfold FlowBoundary
  rw [Finset.sum_sub_distrib]
  have split : ∀ g : V → V → ℝ, ∑ v ∈ W, ∑ u, g v u =
      ∑ v ∈ W, ∑ u ∈ W, g v u + ∑ v ∈ W, ∑ u ∈ Finset.univ.filter (fun u => u ∉ W), g v u := by
    intro g
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ W), Finset.filter_mem_eq_inter,
      Finset.univ_inter]
  rw [split (fun v u => phi v u), split (fun v u => phi u v)]
  have hswap : ∑ v ∈ W, ∑ u ∈ W, phi v u = ∑ v ∈ W, ∑ u ∈ W, phi u v := Finset.sum_comm
  have hzero : ∑ v ∈ W, ∑ u ∈ Finset.univ.filter (fun u => u ∉ W), phi u v = 0 := by
    refine Finset.sum_eq_zero (fun v hv => Finset.sum_eq_zero (fun u hu => ?_))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rcases (hphi v u).2.2 with h | h
    · exfalso; exact hu (hno v hv u ⟨fun e => hu (e ▸ hv), h⟩)
    · exact h
  have hpos : 0 ≤ ∑ v ∈ W, ∑ u ∈ Finset.univ.filter (fun u => u ∉ W), phi v u :=
    Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun u _ => (hphi v u).1))
  linarith

theorem bdy_abs (delta : ℝ) (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (v : V) :
    |FlowBoundary phi v| ≤ ((Fintype.card V : ℝ) - 1) * delta := by
  unfold FlowBoundary
  rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ v),
    diag_zero delta phi hphi v, sub_self, zero_add]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ u ∈ Finset.univ.erase v, |phi v u - phi u v| ≤ delta := by
    intro u _
    have h1 := hphi v u
    have h2 := hphi u v
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2.1, h2.1, h2.2.1]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ,
    nsmul_eq_mul]
  have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  push_cast [Nat.cast_sub this]
  ring

theorem negpart_sub (a b : ℝ) : min 0 a - |b| ≤ min 0 (a - b) := by
  rcases le_total 0 a with h | h <;> rcases le_total 0 (a - b) with h' | h' <;>
    simp only [min_eq_left, min_eq_right, h, h'] <;>
    cases abs_cases b <;> linarith

end IFFFlow

open IFFLib IFFFlow

/-- The common core of Propositions 10.20 and 10.23. -/
theorem iff_core {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [DecidableEq ι]
    (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (delta : ℝ) (hdelta : 0 < delta)
    (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (W : Finset V)
    (hSW : ∀ v, ZVec x phi v ≤ -delta → v ∈ W) (hWT : ∀ v ∈ W, ¬ (delta ≤ ZVec x phi v))
    (hnoarcs : NoArcsLeaving (AphiActive phi) W) (hnoactive : NoActiveTriples I L W) :
    (∑ v, NegPart (ZVec x phi) v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ) * delta ∧
    (∑ v, NegPart x v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ)^2 * delta := by
  have hxW := x_prefix rho hrho I L lam x hx W (prefix_of_no_active I L W hnoactive)
  have hbW := bdy_nonneg delta phi hphi W hnoarcs
  have hzW : (rho W : ℝ) ≤ ∑ v ∈ W, ZVec x phi v := by
    unfold ZVec; rw [Finset.sum_add_distrib, hxW]; linarith
  have h1 : (∑ v, NegPart (ZVec x phi) v) ≥ (rho W : ℝ) - (Fintype.card V : ℝ) * delta := by
    have hterm : ∀ v, (if v ∈ W then ZVec x phi v else 0) - delta ≤ NegPart (ZVec x phi) v := by
      intro v
      unfold DiscreteConvex.AlgorithmsB.NegPart
      by_cases hv : v ∈ W
      · rw [if_pos hv]
        have := hWT v hv
        push Not at this
        rcases le_total 0 (ZVec x phi v) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
      · rw [if_neg hv]
        have : -delta < ZVec x phi v := by
          by_contra hc; push Not at hc; exact hv (hSW v hc)
        rcases le_total 0 (ZVec x phi v) with h | h
        · rw [min_eq_left h]; linarith
        · rw [min_eq_right h]; linarith
    have hs := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hterm v)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at hs
    linarith
  refine ⟨h1, ?_⟩
  have hterm : ∀ v, NegPart (ZVec x phi) v - ((Fintype.card V : ℝ) - 1) * delta ≤ NegPart x v := by
    intro v
    have hx' : x v = ZVec x phi v - FlowBoundary phi v := by unfold ZVec; ring
    unfold DiscreteConvex.AlgorithmsB.NegPart
    rw [hx']
    exact le_trans (by linarith [bdy_abs delta phi hphi v]) (negpart_sub _ _)
  have hs := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hterm v)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [DecidableEq ι]
    (rho : Finset V → ℤ)
    (hrho : Submodular rho) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ)
    (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (delta : ℝ) (hdelta : 0 < delta)
    (phi : V → V → ℝ) (hphi : IsDeltaFeasibleFlow delta phi) (W : Finset V)
    (hSW : ∀ v, ZVec x phi v ≤ -delta → v ∈ W) (hWT : ∀ v ∈ W, ¬ (delta ≤ ZVec x phi v))
    (hnoarcs : NoArcsLeaving (AphiActive phi) W) (hnoactive : NoActiveTriples I L W) (w : V) :
    (x w < -(Fintype.card V : ℝ)^2 * delta → ∀ X : Finset V, (rho X : ℤ) = MinRho rho → w ∈ X) ∧
    (x w > (Fintype.card V : ℝ)^2 * delta → ∀ X : Finset V, (rho X : ℤ) = MinRho rho → w ∉ X) := by
  obtain ⟨-, h2⟩ := iff_core rho hrho I L lam x hx delta hdelta phi hphi W hSW hWT hnoarcs
    hnoactive
  have hle : (MinRho rho : ℝ) ≤ (rho W : ℝ) := by
    exact_mod_cast Finset.inf'_le rho (Finset.mem_univ W)
  have hlow : (MinRho rho : ℝ) - (Fintype.card V : ℝ)^2 * delta ≤ ∑ v, NegPart x v := by
    linarith
  constructor
  · intro hw X hX
    by_contra hwX
    have h1 := neg_le x (insert w X)
    rw [Finset.sum_insert hwX] at h1
    have h3 := x_le rho hrho I L lam x hx X
    rw [hX] at h3
    linarith
  · intro hw X hX hwX
    have h1 := neg_le x (X.erase w)
    have h4 := Finset.add_sum_erase X x hwX
    have h3 := x_le rho hrho I L lam x hx X
    rw [hX] at h3
    linarith

#print axioms solution
