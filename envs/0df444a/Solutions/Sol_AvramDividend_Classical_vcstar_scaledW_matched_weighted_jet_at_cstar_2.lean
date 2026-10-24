-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_scaledW_matched_weighted_jet_at_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:22:51.258985+00:00
-- url     : https://prove2.me/submissions/d8cd18ee-a4c0-476d-a907-f0657b36d899
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_scaledW_boundary_smooth_fit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The IsScaleFunction conjunction supplies W=0 for negative reserves;
the HJB boundary jet is the sole remaining Open mathematical input. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) z) ∧
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by
  constructor
  · intro z hz
    exact vcstar_eq_scaledW_on_Iic_cstar W hW.1 z hz
  · exact vcstar_scaledW_boundary_smooth_fit X hX q hq W hW
      hc hcpos h_smooth
