-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:14:15.975056+00:00
-- url     : https://prove2.me/submissions/8aede4a3-1ffb-484a-b298-abf9606edfc9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_hasDerivAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution (b : Bool) (X g : Mat k r) : Continuous (fun t : ℝ => cv b X t g) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have h := (cv_hasDerivAt b X (cv b X t0 g)).continuousAt
  have e : (fun t : ℝ => cv b X t g) = fun t => cv b X (t - t0) (cv b X t0 g) := by
    funext t; rw [← cv_add]; congr 1; ring
  rw [e]
  exact ContinuousAt.comp_of_eq (g := fun s => cv b X s (cv b X t0 g)) (f := fun t : ℝ => t - t0) h
    ((continuous_sub_right t0).continuousAt) (by ring)
end Formalism.FourierDecayAlt.P.Ux1
