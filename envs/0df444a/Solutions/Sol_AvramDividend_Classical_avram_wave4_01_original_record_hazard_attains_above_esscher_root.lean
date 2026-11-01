-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_hazard_attains_above_esscher_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:49:40.865912+00:00
-- url     : https://prove2.me/submissions/30ba0ba6-e102-4391-bd89-8eadb1b6b70a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_log_rate_continuous
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_hazard_tendsto_esscher_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- Every hazard level above the unrestricted Esscher root is attained at a finite positive drawdown depth. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (targetRate : ℝ) (htargetRate : φ < targetRate) :
    ∃ a : ℝ, 0 < a ∧
      -Real.log ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
        barrierRuinTime X a ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X 1 ω).toReal)))
        else 0 ∂P).toReal) = targetRate := by
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hcont : ContinuousOn K (Ioi (0 : ℝ)) :=
    avram_wave3_01_original_record_log_rate_continuous
      X q hq W hW hnbv hvar
  have hzero : Tendsto K (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    avram_wave4_01_original_record_hazard_tendsto_infinity_zero_depth
      X q hq W hW hvar
  have hinfty : Tendsto K atTop (nhds φ) :=
    avram_wave4_01_original_record_hazard_tendsto_esscher_root
      X q hq W hW hvar φ hφ hroot
  have hnear : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < a ∧ a < 1 ∧ targetRate ≤ K a := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ)),
      (tendsto_atTop.1 hzero targetRate)] with a ha ha1 haK
    exact ⟨ha, ha1, haK⟩
  obtain ⟨a, ha, ha1, haK⟩ := hnear.exists
  have hfar : ∀ᶠ b : ℝ in atTop, 1 ≤ b ∧ K b < targetRate := by
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      hinfty.eventually (eventually_lt_nhds htargetRate)] with b hb hbK
    exact ⟨hb, hbK⟩
  obtain ⟨b, hb, hbK⟩ := hfar.exists
  have hab : a ≤ b := by linarith
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_lt_of_le ha hz.1
  have hcont' : ContinuousOn (fun z : ℝ => -K z) (Icc a b) :=
    (hcont.mono hsub).neg
  have hval : -targetRate ∈ Icc (-K a) (-K b) := by
    constructor
    · linarith
    · linarith
  obtain ⟨c, hc, hceq⟩ := (intermediate_value_Icc hab hcont') hval
  exact ⟨c, lt_of_lt_of_le ha hc.1, by simpa only [K] using neg_inj.mp hceq⟩
