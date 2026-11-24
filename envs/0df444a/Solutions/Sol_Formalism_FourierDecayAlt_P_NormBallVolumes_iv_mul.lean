-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormBallVolumes.iv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:22:52.495082+00:00
-- url     : https://prove2.me/submissions/3c32c087-bcfe-4e6b-b368-40ac5939b902

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftingTheory
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Hsq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NormBallVolumes
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.NormBallVolumes
theorem _root_.solution {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold iv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hsq k r
end Formalism.FourierDecayAlt.P.NormBallVolumes
