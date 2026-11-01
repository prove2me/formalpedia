-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_of_pure_C2_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:08:58.929984+00:00
-- url     : https://prove2.me/submissions/679219fe-6f72-4b8b-9b5f-11d861003f69

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped Topology NNReal ENNReal

/-- Exact cap equality from an explicitly assumed strict-interior equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator (vcstar W) x - q * vcstar W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hcpos.ne' hc.ne
  have hcont :=
    avram_wave4_p3_vcstar_generator_residual_continuousAt_positive_cap_of_pure_C2
      X hX q hq W hW hc hcpos hσ hnbv hC2
  have hposnh : Ioi (0 : ℝ) ∈ 𝓝 (cstar W).toReal :=
    isOpen_Ioi.mem_nhds ha
  have hposwithin : Ioi (0 : ℝ) ∈ 𝓝[<] (cstar W).toReal :=
    nhdsWithin_le_nhds hposnh
  have hevent :
      ∀ᶠ y in 𝓝[<] (cstar W).toReal,
        X.generator (vcstar W) y - q * vcstar W y = 0 := by
    filter_upwards [self_mem_nhdsWithin, hposwithin] with y hylt hypos
    exact hinside y ⟨hypos, hylt⟩
  have htend :
      Filter.Tendsto
        (fun y : ℝ => X.generator (vcstar W) y - q * vcstar W y)
        (𝓝[<] (cstar W).toReal)
        (𝓝 (X.generator (vcstar W) (cstar W).toReal -
          q * vcstar W (cstar W).toReal)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hle :
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal ≤ 0 := by
    apply le_of_tendsto htend
    filter_upwards [hevent] with y hy
    simp [hy]
  have hnegLe :
      -(X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal) ≤ 0 := by
    apply le_of_tendsto htend.neg
    filter_upwards [hevent] with y hy
    simp [hy]
  have hdom :=
    avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
      X q W hW ha hC2
  exact ⟨hdom, le_antisymm hle (by linarith)⟩
