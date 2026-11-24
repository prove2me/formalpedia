-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.wd_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:23.403943+00:00
-- url     : https://prove2.me/submissions/1b2afd01-9fd8-47a9-be6a-b585045c4927

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
theorem _root_.solution (z z' : Vc k r) (hTT : 0 ≤ Tz k r z * Tz k r z') (ρ : ℝ) :
    wd k r z z' (Metric.closedBall 0 ρ) < ∞ := by
  show (volume.withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ))
    (Metric.closedBall 0 ρ) < ∞
  rw [withDensity_apply _ measurableSet_closedBall]
  calc ∫⁻ ζ in Metric.closedBall (0:ℂ) ρ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)
      ≤ ∫⁻ ζ in Metric.closedBall (0:ℂ) ρ, ENNReal.ofReal ((ρ ^ 2) ^ (k - 1)) := by
        refine setLIntegral_mono' measurableSet_closedBall fun ζ hζ => ?_
        apply ENNReal.ofReal_le_ofReal
        have hn : ‖ζ‖ ≤ ρ := by simpa using hζ
        have hq : Complex.normSq ζ ≤ ρ ^ 2 := by
          rw [Complex.normSq_eq_norm_sq]
          nlinarith [norm_nonneg ζ]
        unfold zWeight
        split_ifs with h
        · first
            | exact pow_le_pow_left (by linarith) (by linarith) _
            | exact pow_le_pow_left₀ (by linarith) (by linarith) _
        · positivity
    _ = ENNReal.ofReal ((ρ ^ 2) ^ (k - 1)) * volume (Metric.closedBall (0:ℂ) ρ) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
