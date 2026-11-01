-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_generator_residual_continuousOn_interior_of_pure_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:44:59.034843+00:00
-- url     : https://prove2.me/submissions/815d8ff6-f682-4020-b3e8-205df9171805

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
set_option maxHeartbeats 1000000

/-- Uniform source-generator continuity at every strict interior point,
under original pure-jump unbounded-variation and positive-state C2 hypotheses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn
      (fun x : ℝ => X.generator (vcstar W) x - q * vcstar W x)
      (Ioo 0 (cstar W).toReal) := by
  have ha : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos hcpos.ne' hc.ne
  have hinf :
      (∫⁻ y in Ioo (-1 : ℝ) 0,
        ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
    by_contra hne
    apply hnbv
    exact ⟨hσ, lt_top_iff_ne_top.mpr hne⟩
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_infinite_small_jumps
      X hσ hinf q hq W hW
  have hcont : Continuous (vcstar W) :=
    avram_wave4_p3_vcstar_global_continuous_of_zero_scale_origin
      X hX q hq W hW hc hcpos hzero
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_positive_real_cstar X q W hW ha
  have hneg : ∀ z : ℝ, z < 0 → vcstar W z = 0 := by
    intro z hz
    exact vcstar_eq_zero_of_neg W z hz
  have hnonneg : ∀ z : ℝ, 0 ≤ vcstar W z := by
    intro z
    by_cases hz : z < 0
    · rw [hneg z hz]
    · have hz1 : vcstar W (-1) = 0 := hneg (-1) (by norm_num)
      have hm : (-1 : ℝ) ≤ z := by linarith
      simpa [hz1] using hmono hm
  intro x hx
  let a : ℝ := (cstar W).toReal
  let l : ℝ := x / 2
  let u : ℝ := (x + a) / 2
  let A : ℝ := a + 1
  have hl : 0 < l := by dsimp [l]; linarith [hx.1]
  have hlu : l < u := by dsimp [l, u, a]; linarith [hx.2]
  have hu : u < A := by dsimp [u, A, a]; linarith [hx.2]
  have hlx : l < x := by dsimp [l]; linarith [hx.1]
  have hxu : x < u := by dsimp [u, a]; linarith [hx.2]
  have hC2loc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 A) :=
    hC2.mono (by intro z hz; exact hz.1)
  have hres :
      ContinuousOn
        (fun z : ℝ => X.generator (vcstar W) z - q * vcstar W z)
        (Icc l u) :=
    avram_wave4_p3_generator_residual_continuousOn_compact_of_monotone_global_C2
      X q (vcstar W) hnonneg hmono hcont A l u hl hlu hu hC2loc
  have hnbhd : Icc l u ∈ nhds x := by
    apply Filter.mem_of_superset (Ioo_mem_nhds hlx hxu)
    intro z hz
    exact ⟨hz.1.le, hz.2.le⟩
  exact (hres.continuousAt hnbhd).continuousWithinAt
