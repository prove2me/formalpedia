-- Prove2me | solution 1 for ExploreFirst.FundIneq.lemma_1_fubini
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:40:12.887212+00:00
-- url     : https://prove2.me/submissions/54d5ba12-c644-48ed-835d-808866ab48e6

import Mathlib
import Definitions.Def_ExploreFirst_FundIneq_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory InformationTheory unitInterval
open scoped ENNReal

theorem solution {Γ : Type*} [MeasurableSpace Γ] (P : Measure Γ) [IsProbabilityMeasure P]
    (Z : Γ → ℝ) (hZ : Measurable Z) (hZ01 : ∀ γ, Z γ ∈ Set.Icc (0 : ℝ) 1) :
    (P.prod (volume : Measure unitInterval)).real {p | (p.2 : ℝ) ≤ Z p.1} = ∫ γ, Z γ ∂P := by
  have hmeas : MeasurableSet {p : Γ × unitInterval | (p.2 : ℝ) ≤ Z p.1} :=
    measurableSet_le (measurable_subtype_coe.comp measurable_snd) (hZ.comp measurable_fst)
  have hsec : ∀ γ, (volume : Measure unitInterval)
      (Prod.mk γ ⁻¹' {p : Γ × unitInterval | (p.2 : ℝ) ≤ Z p.1}) = ENNReal.ofReal (Z γ) := by
    intro γ
    have : Prod.mk γ ⁻¹' {p : Γ × unitInterval | (p.2 : ℝ) ≤ Z p.1} =
        Set.Iic (⟨Z γ, hZ01 γ⟩ : unitInterval) := by
      ext x
      exact Iff.rfl
    rw [this, unitInterval.volume_Iic]
  have hint : Integrable Z P :=
    (integrable_const (1 : ℝ)).mono' hZ.aestronglyMeasurable
      (ae_of_all _ (fun γ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hZ01 γ).1]; exact (hZ01 γ).2))
  rw [Measure.real, Measure.prod_apply hmeas]
  simp_rw [hsec]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun γ => (hZ01 γ).1)),
    ENNReal.toReal_ofReal (integral_nonneg (fun γ => (hZ01 γ).1))]
