-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:14:49.921394+00:00
-- url     : https://prove2.me/submissions/9c534607-8498-41e5-8e3b-b9e827250a7a

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C1_sigma_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Interior compact continuity extends to the entire positive half-line. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0)) :
    ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0) := by
  intro x hx
  let l : ℝ := x / 2
  have hx0 : 0 < x := hx
  let u : ℝ := x + 1
  let a : ℝ := x + 2
  have hl : 0 < l := by
    dsimp [l]
    linarith
  have hlu : l < u := by
    dsimp [l, u]
    linarith
  have hu : u < a := by
    dsimp [u, a]
    linarith
  have hC1a : ContDiffOn ℝ 1 W (Ioo 0 a) := by
    apply hC1.mono
    intro z hz
    exact hz.1
  have hK := generator_residual_continuousOn_compact_of_standing_bv_C1_sigma_zero
    X hX hbv hσ q W hW a l u hl hlu hu hC1a
  have hxl : l < x := by
    dsimp [l]
    linarith
  have hxu : x < u := by
    dsimp [u]
    linarith
  have hK_nhds : Icc l u ∈ 𝓝 x := by
    apply Filter.mem_of_superset (Ioo_mem_nhds hxl hxu)
    intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  exact (hK.continuousAt hK_nhds).continuousWithinAt
