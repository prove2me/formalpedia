-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_affine_majorant_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:26:49.862854+00:00
-- url     : https://prove2.me/submissions/1c09276b-4ac1-450d-967b-c651baf97459

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_near_field_jump_nonpos_of_affine_majorant
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_discounted_value_dominates_drift_at_threshold
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤
        z - (cstar W).toReal + vcstar W (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x) (hx1 : 1 ≤ x)
    (hthreshold : (cstar W).toReal + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_positive_real_cstar X q W hW hpos
  have hvalue : X.c ≤ q * vcstar W x :=
    vcstar_discounted_value_dominates_drift_at_threshold
      X q hq W hW hpos x hx hthreshold
  obtain ⟨hint, hres⟩ :=
    vcstar_near_field_jump_nonpos_of_affine_majorant
      X q W hW hmono hchord x hx hx1 hvalue
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  refine ⟨hint, ?_⟩
  rw [hder]
  simpa using (max_eq_right hres :
    max (X.generator (vcstar W) x - q * vcstar W x) 0 = 0)