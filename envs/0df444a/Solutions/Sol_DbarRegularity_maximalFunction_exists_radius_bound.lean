-- Prove2me | solution 1 for DbarRegularity.maximalFunction_exists_radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:23:34.612977+00:00
-- url     : https://prove2.me/submissions/703cf991-07af-411a-bc50-0108e974939c

import Definitions.Def_DbarRegularity_Setting



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Radii realising the maximal function above `α`, with a uniform bound. -/
theorem maximalFunction_exists_radius_bound (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0) (hα : 0 < α)
    (hS : ∫⁻ y, ‖f y‖ₑ ≠ ⊤) :
    ∃ R : ℝ, ∀ x, (α : ℝ≥0∞) < maximalFunction f x → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      (α : ℝ≥0∞) * volume (ball x ρ) < ∫⁻ y in ball x ρ, ‖f y‖ₑ := by
  have key : ∀ x, (α : ℝ≥0∞) < maximalFunction f x → ∃ ρ : ℝ, 0 < ρ ∧
      (α : ℝ≥0∞) * volume (ball x ρ) < ∫⁻ y in ball x ρ, ‖f y‖ₑ := by
    intro x hx
    obtain ⟨r, hr⟩ := lt_iSup_iff.1 hx
    obtain ⟨hr0, hr⟩ := lt_iSup_iff.1 hr
    refine ⟨r, hr0, ?_⟩
    have h0 : volume (ball x r) ≠ 0 := (measure_ball_pos _ _ hr0).ne'
    have ht : volume (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
    rw [← ENNReal.div_eq_inv_mul] at hr
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl h0) (Or.inl ht)).1 hr
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, fun x hx => ?_⟩
    obtain ⟨r, hr0, hr⟩ := key x hx
    have hb : ∀ s : ℝ, 0 < s → ball x s = univ := fun s hs =>
      eq_univ_of_forall fun y => by
        rw [mem_ball, Subsingleton.elim y x, dist_self]; exact hs
    refine ⟨1, one_pos, le_rfl, ?_⟩
    rwa [hb 1 one_pos, ← hb r hr0]
  set c := volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hc0 : c ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hct : c ≠ ⊤ := measure_ball_lt_top.ne
  set K := ((∫⁻ y, ‖f y‖ₑ) / ((α : ℝ≥0∞) * c)).toReal
  refine ⟨max 1 K, fun x hx => ?_⟩
  obtain ⟨r, hr0, hr⟩ := key x hx
  refine ⟨r, hr0, ?_, hr⟩
  have hlt : (α : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * c) < ∫⁻ y, ‖f y‖ₑ := by
    have hB : volume (ball x r) = ENNReal.ofReal (r ^ d) * c := by
      rw [Measure.addHaar_ball_of_pos _ _ hr0, finrank_euclideanSpace_fin]
    rw [← hB]
    exact hr.trans_le (setLIntegral_le_lintegral _ _)
  have hαc0 : (α : ℝ≥0∞) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hα.ne') hc0
  have hαct : (α : ℝ≥0∞) * c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hct
  have h1 : ENNReal.ofReal (r ^ d) < (∫⁻ y, ‖f y‖ₑ) / ((α : ℝ≥0∞) * c) := by
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hαc0) (Or.inl hαct)]
    calc ENNReal.ofReal (r ^ d) * ((α : ℝ≥0∞) * c)
        = (α : ℝ≥0∞) * (ENNReal.ofReal (r ^ d) * c) := by ring
      _ < _ := hlt
  have h2 : r ^ d < K := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (ENNReal.div_ne_top hS hαc0)] at h1
    exact h1
  rcases le_or_gt r 1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact (le_self_pow₀ h.le hd.ne').trans (h2.le.trans (le_max_right _ _))

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric
open scoped ENNReal NNReal

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0) (hα : 0 < α)
    (hS : ∫⁻ y, ‖f y‖ₑ ≠ ⊤) :
    ∃ R : ℝ, ∀ x, (α : ℝ≥0∞) < maximalFunction f x → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧
      (α : ℝ≥0∞) * volume (ball x ρ) < ∫⁻ y in ball x ρ, ‖f y‖ₑ :=
  maximalFunction_exists_radius_bound d f α hα hS
