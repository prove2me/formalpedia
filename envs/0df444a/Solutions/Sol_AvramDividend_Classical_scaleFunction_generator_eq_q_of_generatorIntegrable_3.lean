-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_generatorIntegrable
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:52:20.235001+00:00
-- url     : https://prove2.me/submissions/f2a8822a-e7e0-49a5-9dc7-7d82bf10c6e2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-- Reduce generator q-harmonicity to the raw stopped-scale expectation
and its local Dynkin consequence. The imported obligations remain Open. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 W (Ioo 0 a))
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 := by
  have hstop : ∀ b y : ℝ, 0 < b → 0 ≤ y → y ≤ b →
      twoSidedExitExpectationCorrected X q b y *
        ENNReal.ofReal (W b) = ENNReal.ofReal (W y) := by
    intro b y hb hy0 hyb
    have hraw := two_sided_exit_stopped_scale_identity
      X hX q hq W hW b y hb hy0 hyb
    have heq :
        twoSidedExitExpectationCorrected X q b y =
          (∫⁻ ω,
            if (⨅ (t : ℝ≥0) (_ : b - y < X.X t ω), (t : ℝ≥0∞)) <
                (⨅ (t : ℝ≥0) (_ : X.X t ω < -y), (t : ℝ≥0∞)) then
              ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : b - y < X.X t ω), (t : ℝ≥0∞)))))
            else 0 ∂P) := by
      unfold twoSidedExitExpectationCorrected
      apply lintegral_congr
      intro ω
      by_cases hc :
          twoSidedExitUpTimeCorrected X (b - y) ω <
            twoSidedExitDownTimeCorrected X (-y) ω
      · have hc' :
            (⨅ (t : ℝ≥0) (_ : b - y < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -y), (t : ℝ≥0∞)) := by
          simpa only [twoSidedExitUpTimeCorrected, twoSidedExitUpTime,
            twoSidedExitDownTimeCorrected, twoSidedExitDownTime] using hc
        simp only [if_pos hc, if_pos hc']
        rfl
      · have hc' :
            ¬ ((⨅ (t : ℝ≥0) (_ : b - y < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -y), (t : ℝ≥0∞))) := by
          simpa only [twoSidedExitUpTimeCorrected, twoSidedExitUpTime,
            twoSidedExitDownTimeCorrected, twoSidedExitDownTime] using hc
        simp only [if_neg hc, if_neg hc']
    rw [heq]
    exact hraw
  exact scaleFunction_generator_eq_q_of_stoppedScaleIdentity_corrected
    X hX q hq W hW a ha h_smooth hint hstop
