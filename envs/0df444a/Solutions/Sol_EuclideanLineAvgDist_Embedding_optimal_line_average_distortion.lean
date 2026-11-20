-- Prove2me | solution 1 for EuclideanLineAvgDist.Embedding.optimal_line_average_distortion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T16:12:16.923185+00:00
-- url     : https://prove2.me/submissions/9ce49bd2-f0e2-4235-841b-201c02ac85a7

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Projection
import Theorems.Thm_EuclideanLineAvgDist_Embedding_dense_ball_embedding
import Theorems.Thm_EuclideanLineAvgDist_Embedding_well_spread_matching
import Theorems.Thm_EuclideanLineAvgDist_Embedding_matching_lipschitz_duality

section
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist
open EuclideanLineAvgDist.Embedding

namespace Dev.Goal

theorem one_lt_log_of_three_le (m : ℝ) (h : 3 ≤ m) : 1 < Real.log m := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  exact lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num; linarith)

theorem one_le_logRate (n : ℕ) : 1 ≤ logRate n := by
  unfold logRate
  have h3 : (3 : ℝ) ≤ max 3 (n : ℝ) := le_max_left _ _
  have hL := one_lt_log_of_three_le _ h3
  set L := Real.log (max 3 (n : ℝ)) with hLdef
  have hpos : 0 < Real.log L := Real.log_pos hL
  have hle : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [one_le_div hpos]
  linarith

theorem extreme_le (n : ℕ) (h : 3 ≤ n) : 2 * extremeCount n ≤ n := by
  have h1 : ((extremeCount n : ℕ) : ℝ) < (n : ℝ) / 64 + 1 := by
    unfold extremeCount
    exact Nat.ceil_lt_add_one (by positivity)
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast h
  have : (2 * extremeCount n : ℝ) < n := by linarith
  have : 2 * extremeCount n < n := by exact_mod_cast this
  omega

theorem disjoint_low_high {k : ℕ} (X : Finset (Eucl k)) (tie : X → ℕ) (g : Eucl k)
    (h : 3 ≤ X.card) : Disjoint (lowSet X tie g) (highSet X tie g) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [lowSet, highSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
  have := extreme_le X.card h
  omega

theorem sum_diff_le {Y : Type*} [Fintype Y] [DecidableEq Y] (A B : Finset Y) (hd : Disjoint A B)
    (hcard : A.card = B.card) (f : Y → ℝ) (z : Y) :
    ∑ y ∈ B, f y - ∑ x ∈ A, f x ≤ ∑ x : Y, |f x - f z| := by
  have e1 : ∑ y ∈ B, f y - ∑ x ∈ A, f x
      = ∑ y ∈ B, (f y - f z) + ∑ x ∈ A, (f z - f x) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  have e2 : ∑ y ∈ B, (f y - f z) ≤ ∑ y ∈ B, |f y - f z| :=
    Finset.sum_le_sum (fun y _ => le_abs_self _)
  have e3 : ∑ x ∈ A, (f z - f x) ≤ ∑ x ∈ A, |f x - f z| :=
    Finset.sum_le_sum (fun x _ => by rw [abs_sub_comm]; exact le_abs_self _)
  have e4 : ∑ y ∈ B, |f y - f z| + ∑ x ∈ A, |f x - f z| = ∑ x ∈ A ∪ B, |f x - f z| := by
    rw [Finset.sum_union hd]; ring
  have e5 : ∑ x ∈ A ∪ B, |f x - f z| ≤ ∑ x : Y, |f x - f z| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => abs_nonneg _)
  linarith

end Dev.Goal

open Dev.Goal in
theorem chk_optimal_line_average_distortion :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 1 ≤ k → ∀ X : Finset (Eucl k),
      ∃ f : X → ℝ, NonExpansive f ∧
        distSum X ≤ C * Real.sqrt (logRate X.card) * lineSpread f := by
  obtain ⟨c1, hc1, H1⟩ := Embedding.well_spread_matching
  refine ⟨256 + 1 / c1, by positivity, ?_⟩
  intro k _ X
  classical
  have hLge : 1 ≤ Real.sqrt (logRate X.card) := by
    rw [Real.one_le_sqrt]; exact one_le_logRate _
  have hSnn : ∀ f : X → ℝ, 0 ≤ lineSpread f := fun f =>
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hc1' : 0 ≤ 1 / c1 := by positivity
  by_cases hD0 : distSum X ≤ 0
  · refine ⟨fun _ => 0, fun x y => by simp, ?_⟩
    have : lineSpread (fun _ : X => (0 : ℝ)) = 0 := by simp [lineSpread]
    rw [this, mul_zero]; exact hD0
  push Not at hD0
  by_cases hA : ∃ x : X, (X.card : ℝ) / 64 ≤ ((ball x (avgDist X / 4)).card : ℝ)
  · obtain ⟨x, hx⟩ := hA
    obtain ⟨hne, hle⟩ := Embedding.dense_ball_embedding (X := X) (1 / 64) 4 (by norm_num)
      (by norm_num) x (by rw [Fintype.card_coe]; linarith)
    refine ⟨_, hne, ?_⟩
    have e : (1 / ((1 / 64 / 2 : ℝ) * (1 - 2 / 4))) = 256 := by norm_num
    rw [e] at hle
    have h1 := mul_nonneg (hSnn (distToFinset (ball x (avgDist X / 4)))) (sub_nonneg.2 hLge)
    have h2 := mul_nonneg (hSnn (distToFinset (ball x (avgDist X / 4))))
      (mul_nonneg hc1' (le_trans zero_le_one hLge))
    nlinarith
  push Not at hA
  -- well spread case
  have hnpos : 0 < X.card := by
    rcases Nat.eq_zero_or_pos X.card with h | h
    · exfalso
      have : IsEmpty X := by rw [← Fintype.card_coe] at h; exact Fintype.card_eq_zero_iff.mp h
      simp [distSum] at hD0
    · exact h
  have hnR : (0 : ℝ) < X.card := by exact_mod_cast hnpos
  have hΔ : 0 < avgDist X := by
    unfold avgDist; rw [Fintype.card_coe]; positivity
  have hn64 : 64 < X.card := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hnpos
    have h1 := hA ⟨x, hx⟩
    have h2 : 1 ≤ (ball (⟨x, hx⟩ : X) (avgDist X / 4)).card := by
      apply Finset.card_pos.mpr
      refine ⟨⟨x, hx⟩, ?_⟩
      simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, dist_self]
      positivity
    have h3 : (1 : ℝ) ≤ ((ball (⟨x, hx⟩ : X) (avgDist X / 4)).card : ℝ) := by exact_mod_cast h2
    have : (64 : ℝ) < X.card := by linarith
    exact_mod_cast this
  have hn65' : (65 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast (show 65 ≤ X.card by omega)
  set n : ℝ := (X.card : ℝ) with hn
  have hn65 : (65 : ℝ) ≤ n := hn65'
  set Δ := avgDist X with hΔdef
  let tie : X → ℕ := fun x => (Fintype.equivFin X x : ℕ)
  have htie : Function.Injective tie := fun a b hab =>
    (Fintype.equivFin X).injective (Fin.ext hab)
  have hlogn : 1 < Real.log n := one_lt_log_of_three_le n (by linarith)
  have hloglog : 0 < Real.log (Real.log n) := Real.log_pos hlogn
  set s := Real.sqrt (Real.log (Real.log n) / Real.log n) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (div_pos hloglog (by linarith))
  set b := c1 * n * Δ * s with hb
  have hbpos : 0 < b := by positivity
  have hex : ∃ g : Eucl k, b ≤ minMatchingCost (lowSet X tie g) (highSet X tie g) := by
    by_contra hne
    push Not at hne
    have H := H1 k X tie htie (fun x => hA x)
    unfold expectedExtremeMatching at H
    have hlt : ∀ g : Eucl k, ENNReal.ofReal (minMatchingCost (lowSet X tie g) (highSet X tie g))
        < ENNReal.ofReal b := fun g => (ENNReal.ofReal_lt_ofReal_iff hbpos).2 (hne g)
    have hle : ∫⁻ g, ENNReal.ofReal (minMatchingCost (lowSet X tie g) (highSet X tie g))
        ∂(stdGaussian (Eucl k)) ≤ ENNReal.ofReal b := by
      calc _ ≤ ∫⁻ g, ENNReal.ofReal b ∂(stdGaussian (Eucl k)) :=
            lintegral_mono (fun g => (hlt g).le)
        _ = ENNReal.ofReal b := by simp
    have hfin : ∫⁻ g, ENNReal.ofReal (minMatchingCost (lowSet X tie g) (highSet X tie g))
        ∂(stdGaussian (Eucl k)) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have hstrict := lintegral_strict_mono_of_ae_le_of_frequently_ae_lt
      (μ := stdGaussian (Eucl k))
      (f := fun g => ENNReal.ofReal (minMatchingCost (lowSet X tie g) (highSet X tie g)))
      (g := fun _ => ENNReal.ofReal b) aemeasurable_const hfin
      (Filter.Eventually.of_forall (fun g => (hlt g).le))
      (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun g => (hlt g).ne)))
    simp only [lintegral_const, measure_univ, mul_one] at hstrict
    exact absurd (lt_of_le_of_lt H hstrict) (lt_irrefl _)
  obtain ⟨g, hg⟩ := hex
  set A := lowSet X tie g with hAdef
  set B := highSet X tie g with hBdef
  have hdisj : Disjoint A B := disjoint_low_high X tie g (by omega)
  -- existence of a matching
  have hmmc : 0 < minMatchingCost A B := lt_of_lt_of_le hbpos hg
  have hne : Nonempty (A ≃ B) := by
    by_contra h
    rw [not_nonempty_iff] at h
    unfold minMatchingCost at hmmc
    rw [Real.iInf_of_isEmpty] at hmmc
    exact lt_irrefl _ hmmc
  obtain ⟨M, hMeq⟩ := exists_eq_ciInf_of_finite (f := fun M : A ≃ B => matchingCost M)
  have hMmin : IsMinMatching M := fun M' => by
    rw [hMeq]
    exact ciInf_le (Set.finite_range _).bddBelow M'
  obtain ⟨f, hfne, hfsum⟩ := Embedding.matching_lipschitz_duality A B hdisj M hMmin
  refine ⟨f, hfne, ?_⟩
  have hcard : A.card = B.card := by
    have := Fintype.card_congr M
    simpa using this
  have hcost : b ≤ ∑ y ∈ B, f y - ∑ x ∈ A, f x := by
    rw [hfsum]
    have : matchingCost M = minMatchingCost A B := by
      rw [minMatchingCost]; exact hMeq
    show b ≤ matchingCost M
    rw [this]; exact hg
  have hSf : n * b ≤ lineSpread f := by
    have h1 : ∀ z : X, b ≤ ∑ x : X, |f x - f z| :=
      fun z => hcost.trans (sum_diff_le A B hdisj hcard f z)
    have h2 : ∑ _z : X, b ≤ ∑ z : X, ∑ x : X, |f x - f z| := Finset.sum_le_sum (fun z _ => h1 z)
    rw [Finset.sum_comm] at h2
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    rw [Fintype.card_coe] at h2
    exact h2
  -- final arithmetic
  have hLR : Real.sqrt (logRate X.card) * s = 1 := by
    have hm : max 3 (X.card : ℝ) = n := max_eq_right (by linarith)
    unfold logRate
    rw [hm, hs, ← Real.sqrt_mul (by positivity)]
    have : Real.log n / Real.log (Real.log n) * (Real.log (Real.log n) / Real.log n) = 1 := by
      field_simp
    rw [this, Real.sqrt_one]
  have hD : distSum X = n ^ 2 * Δ := by
    rw [hΔdef, avgDist, Fintype.card_coe]; field_simp; rfl
  set R := Real.sqrt (logRate X.card) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hS0 := hSnn f
  -- c1 * s * D ≤ S_f
  have h1 : c1 * s * distSum X ≤ lineSpread f := by
    have : n * b = n * (c1 * n * Δ * s) := rfl
    rw [hD]; nlinarith
  have h2 : distSum X = (1 / c1) * R * (c1 * s * distSum X) := by
    field_simp
    nlinarith [hLR]
  have h3 : (1 / c1) * R * (c1 * s * distSum X) ≤ (1 / c1) * R * lineSpread f :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h4 : 0 ≤ 256 * R * lineSpread f := by positivity
  nlinarith

end EuclideanLineAvgDist

end

theorem solution : type_of% @EuclideanLineAvgDist.chk_optimal_line_average_distortion := @EuclideanLineAvgDist.chk_optimal_line_average_distortion
