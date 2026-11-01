-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_hazard_chord_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:53:24.736677+00:00
-- url     : https://prove2.me/submissions/da4da1c4-bbfb-4b71-850a-de65cc8b7095

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_log_hazard_antitone_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_eq_log_scale_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- The actual drawdown hazard bounds every forward logarithmic scale chord. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (Real.log (W b) - Real.log (W a)) / (b - a) ≤
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                      barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) := by
  let F : ℝ → ℝ := fun x => Real.log (W x)
  let K : ℝ → ℝ := fun x => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X x ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hanti : AntitoneOn K (Ioi (0 : ℝ)) :=
    avram_wave4_01_original_record_log_hazard_antitone_depth X q hq W hW hnbv
  have hD : ∀ x : ℝ, 0 < x → HasDerivAt F (K x) x := by
    intro x hx
    exact avram_wave4_01_original_record_hazard_eq_log_scale_deriv
      X q hq W hW hvar x hx
  have hcont : ContinuousOn F (Icc a b) := by
    intro x hx
    exact ((hD x (lt_of_lt_of_le ha hx.1)).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (Ioo a b) := by
    intro x hx
    exact ((hD x (lt_trans ha hx.1)).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hmean⟩ := exists_deriv_eq_slope F hab hcont hdiff
  have hkc : deriv F c = K c := (hD c (lt_trans ha hc.1)).deriv
  have hca : K c ≤ K a :=
    hanti (show a ∈ Ioi (0 : ℝ) from ha)
      (show c ∈ Ioi (0 : ℝ) from lt_trans ha hc.1) hc.1.le
  change (F b - F a) / (b - a) ≤ K a
  rw [← hmean, hkc]
  exact hca
