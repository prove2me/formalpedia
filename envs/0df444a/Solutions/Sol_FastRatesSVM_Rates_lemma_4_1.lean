-- Prove2me | solution 1 for FastRatesSVM.Rates.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:44:24.165994+00:00
-- url     : https://prove2.me/submissions/a3b27fac-df58-4e3e-a249-30b31541d0d3

import Mathlib
import Definitions.Def_FastRatesSVM_Rates_Extension

set_option autoImplicit false

open FastRatesSVM.Rates

lemma frs_proj_le {d : ℕ} (x y : E d) (hx : ‖x‖ ≤ 1) (hy : 1 < ‖y‖) :
    ‖x - ‖y‖⁻¹ • y‖ ≤ ‖x - y‖ := by
  set r : ℝ := ‖y‖ with hr
  have hr0 : 0 < r := by linarith
  have ha : inner ℝ x y ≤ r := by
    calc inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      _ ≤ 1 * r := by gcongr
      _ = r := one_mul r
  have h1 : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + r ^ 2 := by
    rw [norm_sub_sq_real]
  have h2 : ‖x - r⁻¹ • y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (r⁻¹ * inner ℝ x y) + 1 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, norm_inv, norm_norm, mul_pow]
    have : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp
    rw [this]
  have key : ‖x - r⁻¹ • y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [h1, h2]
    have hinv : 0 < 1 - r⁻¹ := by
      have : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hy
      linarith
    have h3 : (1 - r⁻¹) * inner ℝ x y ≤ (1 - r⁻¹) * r := by gcongr
    have h4 : (1 - r⁻¹) * r = r - 1 := by field_simp
    nlinarith [sq_nonneg (r - 1)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 key


lemma frs_ball_aux {d : ℕ} (x : E d) (hx : ‖x‖ ≤ 1) (S : Set (E d)) (hS : S ⊆ X d) :
    ∀ y ∈ Metric.ball x (Metric.infDist x S),
      ‖y‖ ≤ 3 ∧ (‖y‖ ≤ 1 → y ∉ S) ∧ (1 < ‖y‖ → ‖y‖⁻¹ • y ∉ S) := by
  intro y hy
  rw [Metric.mem_ball] at hy
  have hxy : dist x y < Metric.infDist x S := by rwa [dist_comm]
  have hSsub : ∀ s ∈ S, ‖s‖ ≤ 1 := fun s hs => by
    have := hS hs
    simpa [X] using this
  refine ⟨?_, ?_, ?_⟩
  · rcases S.eq_empty_or_nonempty with h | h
    · subst h
      simp at hxy
      exact absurd hxy (not_lt.2 dist_nonneg)
    · obtain ⟨s, hs⟩ := h
      have h1 : Metric.infDist x S ≤ dist x s := Metric.infDist_le_dist_of_mem hs
      have h2 : dist x s ≤ 2 := by
        rw [dist_eq_norm]
        calc ‖x - s‖ ≤ ‖x‖ + ‖s‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith [hSsub s hs]
      have h3 : ‖y‖ ≤ ‖x‖ + dist x y := by
        calc ‖y‖ = ‖x + (y - x)‖ := by simp
          _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
          _ = ‖x‖ + dist x y := by rw [dist_comm, dist_eq_norm]
      linarith
  · intro hy1 hyS
    have := Metric.infDist_le_dist_of_mem (x := x) hyS
    linarith
  · intro hy1 hzS
    have h1 := Metric.infDist_le_dist_of_mem (x := x) hzS
    have h2 : dist x (‖y‖⁻¹ • y) ≤ dist x y := by
      rw [dist_eq_norm, dist_eq_norm]
      exact frs_proj_le x y hx hy1
    linarith

/-- Lemma 4.1, arXiv:0708.1838v1, p. 15. -/
theorem solution (d : ℕ) (hd : 0 < d) (D : BinaryDistribution d) :
    (∀ x ∈ Xplus D, Metric.ball x (tau D x) ⊆ extendedPlus D) ∧
    (∀ x ∈ Xminus D, Metric.ball x (tau D x) ⊆ extendedMinus D) := by
  classical
  constructor
  · intro x hx y hy
    have hxX : ‖x‖ ≤ 1 := by simpa [X] using hx.1
    have hxm : x ∉ Xminus D := fun h => by
      have := h.2; have := hx.2; linarith
    have htau : tau D x = Metric.infDist x (Xzero D ∪ Xminus D) := by
      unfold tau; simp [hxm, hx]
    rw [htau] at hy
    have hS : (Xzero D ∪ Xminus D) ⊆ X d := fun s hs => by
      rcases hs with h | h <;> exact h.1
    obtain ⟨h3, hA, hB⟩ := frs_ball_aux x hxX _ hS y hy
    refine ⟨by simpa [extendedX] using h3, ?_⟩
    have good : ∀ z : E d, ‖z‖ ≤ 1 → z ∉ (Xzero D ∪ Xminus D) → 1 / 2 < D.η z := by
      intro z hz hzS
      have hzX : z ∈ X d := by simpa [X] using hz
      by_contra hcon
      have hcon := not_lt.1 hcon
      apply hzS
      rcases hcon.lt_or_eq with h | h
      · exact Or.inr ⟨hzX, h⟩
      · exact Or.inl ⟨hzX, h⟩
    unfold extendedEta
    split_ifs with h1
    · exact good y h1 (hA h1)
    · have h1 := not_le.1 h1
      refine good _ ?_ (hB h1)
      rw [norm_smul, norm_inv, norm_norm]
      rw [inv_mul_cancel₀ (by linarith)]
  · intro x hx y hy
    have hxX : ‖x‖ ≤ 1 := by simpa [X] using hx.1
    have hxp : x ∉ Xplus D := fun h => by
      have := h.2; have := hx.2; linarith
    have hnz : x ∉ Xzero D := fun h => by
      have := h.2; have := hx.2; linarith
    have htau : tau D x = Metric.infDist x (Xzero D ∪ Xplus D) := by
      unfold tau; simp [hx]
    rw [htau] at hy
    have hS : (Xzero D ∪ Xplus D) ⊆ X d := fun s hs => by
      rcases hs with h | h <;> exact h.1
    obtain ⟨h3, hA, hB⟩ := frs_ball_aux x hxX _ hS y hy
    refine ⟨by simpa [extendedX] using h3, ?_⟩
    have good : ∀ z : E d, ‖z‖ ≤ 1 → z ∉ (Xzero D ∪ Xplus D) → D.η z < 1 / 2 := by
      intro z hz hzS
      have hzX : z ∈ X d := by simpa [X] using hz
      by_contra hcon
      have hcon := not_lt.1 hcon
      apply hzS
      rcases hcon.lt_or_eq with h | h
      · exact Or.inr ⟨hzX, h⟩
      · exact Or.inl ⟨hzX, h.symm⟩
    unfold extendedEta
    split_ifs with h1
    · exact good y h1 (hA h1)
    · have h1 := not_le.1 h1
      refine good _ ?_ (hB h1)
      rw [norm_smul, norm_inv, norm_norm]
      rw [inv_mul_cancel₀ (by linarith)]

