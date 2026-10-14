-- Prove2me | solution 1 for DbarRegularity.maximalFunction_ae_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:08:33.79373+00:00
-- url     : https://prove2.me/submissions/433f3028-3957-4b23-8187-b36c4f06249c

import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_DbarRegularity_maximalFunction_lowerSemicontinuous
import Theorems.Thm_DbarRegularity_maximalFunction_le_eLpNorm_top
import Theorems.Thm_DbarRegularity_maximalFunction_weakType_one
import Theorems.Thm_DbarRegularity_maximalFunction_strongType



namespace DbarRegularity

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- The maximal function of an `L^p` function, `1 ≤ p ≤ ∞`, is finite almost everywhere. -/
theorem maximalFunction_ae_lt_top (d : ℕ) :
    ∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      ∀ᵐ x, maximalFunction f x < ⊤ := by
  intro p hp f hf
  rcases eq_or_ne p ⊤ with rfl | hpt
  · exact ae_of_all _ fun x => (maximalFunction_le_eLpNorm_top d f x).trans_lt hf.2
  rcases hp.eq_or_lt with rfl | hp1
  · -- `p = 1`
    have hS : ∫⁻ x, ‖f x‖ₑ ≠ ⊤ := by
      rw [← eLpNorm_one_eq_lintegral_enorm]; exact hf.2.ne
    rw [ae_iff]
    set E := {x | ¬ maximalFunction f x < ⊤}
    have hbound : ∀ n : ℕ, volume E ≤
        (5 : ℝ≥0∞) ^ d * (∫⁻ x, ‖f x‖ₑ) * ((n : ℝ≥0∞) + 1)⁻¹ := by
      intro n
      have h := maximalFunction_weakType_one d f ((n : ℝ≥0) + 1) (by positivity)
      push_cast at h
      refine (measure_mono fun x hx => ?_).trans (h.trans_eq ?_)
      · simp only [E, Set.mem_setOf_eq, not_lt, top_le_iff] at hx ⊢
        rw [hx]
        exact ENNReal.add_lt_top.2 ⟨ENNReal.natCast_lt_top n, ENNReal.one_lt_top⟩
      · rw [ENNReal.div_eq_inv_mul]; ring
    have ht : Tendsto (fun n : ℕ => (5 : ℝ≥0∞) ^ d * (∫⁻ x, ‖f x‖ₑ) * ((n : ℝ≥0∞) + 1)⁻¹)
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
      simpa using ENNReal.Tendsto.const_mul h0
        (Or.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hS))
    exact le_antisymm (ge_of_tendsto' ht hbound) bot_le
  · -- `1 < p < ∞`
    obtain ⟨A, hA⟩ := maximalFunction_strongType d p hp1
    have hM := (hA f hf).1
    have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
    have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
    have hint := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpt hM.2
    simp only [enorm_eq_self] at hint
    have hmeas := (maximalFunction_lowerSemicontinuous d f).measurable
    filter_upwards [ae_lt_top (hmeas.pow_const p.toReal) hint.ne] with x hx
    exact (ENNReal.rpow_lt_top_iff_of_pos hr).1 hx

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution (d : ℕ) :
    ∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      ∀ᵐ x, maximalFunction f x < ⊤ :=
  maximalFunction_ae_lt_top d
