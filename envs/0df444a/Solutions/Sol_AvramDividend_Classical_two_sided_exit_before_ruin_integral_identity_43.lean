-- Prove2me | solution 43 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:35:51.082991+00:00
-- url     : https://prove2.me/submissions/37cdbe64-c2ee-423a-be7e-1553744f06f8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_stopped_scale_identity_to_ratio

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

-- Integral identity via Open stopped-scale identity divided by Proved ratio bridge.
-- hStop (Open 09663d0d): J * ofReal (W a) = ofReal (W x) for the same iSup-clock
-- integral J. hpos (Proved 59531c77): 0 < W a under Standing. The Proved pure
-- bridge 212e3098 (stopped_scale_identity_to_ratio) closes J = ofReal (W x / W a)
-- in one step, avoiding the generic GroupWithZero division lemmas that caused the
-- 18019/18047/18061/18063 schematic-?m/?u CE chain. Fresh causal hypothesis.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION. No local Lean was run.
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
  have hStop :=
    AvramDividend.Classical.two_sided_exit_stopped_scale_identity
      X hX q hq W hW a x ha hx0 hxa
  have hpos :=
    AvramDividend.Classical.scaleFunction_strict_pos_of_standing
      X hX q hq W hW a ha
  exact AvramDividend.Classical.stopped_scale_identity_to_ratio
    _ _ _ hStop hpos
