-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_eventual_hjb_finite_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:39:05.069009+00:00
-- url     : https://prove2.me/submissions/e5ce93c7-e79f-4d60-abd6-386051424f09

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_vcstar_far_field_hjb_of_reserve_drift_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The HJB equation is automatically satisfied at all sufficiently large
reserves for any finite optimal barrier and any Lévy drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hcfin : cstar W < ⊤)
    (x : ℝ)
    (hx : (cstar W).toReal + 1 + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hmax0 : (0 : ℝ) ≤ max 0 (X.c / q) := le_max_left _ _
  have hmaxc : X.c / q ≤ max 0 (X.c / q) := le_max_right _ _
  have hfar : (cstar W).toReal + 1 ≤ x := by linarith
  have hquot : X.c / q ≤ x - (cstar W).toReal := by linarith
  have hdrift : X.c ≤ q * (x - (cstar W).toReal) := by
    simpa [mul_comm] using ((div_le_iff₀ hq).mp hquot)
  exact vcstar_far_field_hjb_of_reserve_drift_bound
    X hX q hq W hW hcfin x hfar hdrift
