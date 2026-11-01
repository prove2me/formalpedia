-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousAt_cap_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:20:19.369738+00:00
-- url     : https://prove2.me/submissions/fdd49522-2514-4e6b-9d56-6311960e54c8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_global_smooth_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hnbv : ¬ X.BoundedVariation)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousAt
      (fun x : ℝ => X.generator (vcstar W) x - q * vcstar W x)
      (cstar W).toReal := by
  have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hcpos.ne' hc.ne
  have hzero : W 0 = 0 := by
    by_cases hσpos : 0 < X.σ
    · exact scaleFunction_zero_origin_gaussian_without_standing
        X q hq W hW hσpos
    · have hσzero : X.σ = 0 :=
        le_antisymm (le_of_not_gt hσpos) X.σ_nonneg
      have hinf :
          (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
        by_contra hne
        apply hnbv
        exact ⟨hσzero, lt_top_iff_ne_top.mpr hne⟩
      exact scaleFunction_zero_origin_infinite_small_jumps
        X hσzero hinf q hq W hW
  have hcont : Continuous (vcstar W) :=
    avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
      X hX q hq W hW hc hcpos hzero
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_positive_real_cstar X q W hW ha
  have hnonneg : ∀ z : ℝ, 0 ≤ vcstar W z := by
    intro z
    by_cases hz : z < 0
    · rw [vcstar_eq_zero_of_neg W z hz]
    · have hz1 : vcstar W (-1) = 0 :=
        vcstar_eq_zero_of_neg W (-1) (by norm_num)
      have hm : (-1 : ℝ) ≤ z := by linarith
      simpa [hz1] using hmono hm
  have hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0) :=
    (vcstar_global_smooth_of_positive_cstar
      X hX q hq W hW hc hcpos h_smooth).1 hnbv
  let a : ℝ := (cstar W).toReal
  let l : ℝ := a / 2
  let u : ℝ := a + 1
  let A : ℝ := a + 2
  have hl : 0 < l := by dsimp [l, a]; linarith
  have hlu : l < u := by dsimp [l, u, a]; linarith
  have hu : u < A := by dsimp [u, A]; linarith
  have hla : l < a := by dsimp [l, a]; linarith
  have hau : a < u := by dsimp [u]; linarith
  have hC2loc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 A) :=
    hC2.mono (by intro z hz; exact hz.1)
  have hres : ContinuousOn
      (fun x : ℝ => X.generator (vcstar W) x - q * vcstar W x)
      (Icc l u) :=
    avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
      X q (vcstar W) hnonneg hmono hcont A l u hl hlu hu hC2loc
  have hnbhd : Icc l u ∈ nhds a := by
    apply Filter.mem_of_superset (Ioo_mem_nhds hla hau)
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  exact hres.continuousAt hnbhd
