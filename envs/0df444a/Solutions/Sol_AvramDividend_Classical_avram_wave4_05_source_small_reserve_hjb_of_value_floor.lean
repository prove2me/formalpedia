-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_small_reserve_hjb_of_value_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:40:52.554977+00:00
-- url     : https://prove2.me/submissions/509cbd7d-4a7f-423a-8279-4004145d72ea

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_left_affine_majorant_of_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_near_field_jump_nonpos_of_unit_value
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The source gradient and global monotonicity hypotheses convert the
value-floor ruin-crossing estimate to HJB, including reserves below one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hunit : 1 ≤ vcstar W x)
    (hbound : X.c ≤ q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hcont :
      ContinuousOn (vcstar W) (Icc 0 (cstar W).toReal) :=
    vcstar_continuousOn_Icc_below_positive_cstar X q W hW hpos
  have hdiff : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
      DifferentiableAt ℝ (vcstar W) z := by
    intro z hz
    exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).1
  have hder : ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
      1 ≤ deriv (vcstar W) z := by
    intro z hz
    exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).2
  have hchord :=
    left_affine_majorant_of_deriv_ge_one
      (vcstar W) (cstar W).toReal (le_of_lt hpos) hcont hdiff hder
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_positive_real_cstar X q W hW hpos
  obtain ⟨hdom, hgen⟩ :=
    vcstar_near_field_jump_nonpos_of_unit_value
      X q W hW hmono hchord x hx hunit hbound
  refine ⟨hdom, ?_⟩
  have hgrad := vcstar_deriv_eq_one_above_cstar W x hx
  simpa [hgrad] using (max_eq_right hgen)
