-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanBoundsLimits.lim_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:26.233725+00:00
-- url     : https://prove2.me/submissions/8959eb57-3ac4-403c-9be4-5668902a5aa4

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanBoundsLimits
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanBoundsLimits_bdd_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanBoundsLimits
open Classical
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {LIM : (Λ → ℂ) → ℂ}
namespace Formalism.FourierDecayAlt.P.MeanBoundsLimits
theorem _root_.solution (hM : IsMean LIM) (c : ℂ) : LIM (fun _ : Λ => c) = c := by
  have e : (fun _ : Λ => c) = c • (fun _ : Λ => (1 : ℂ)) := by funext; simp
  rw [e, hM.2.1 c _ (bdd_const 1), hM.2.2.2.1, mul_one]
end Formalism.FourierDecayAlt.P.MeanBoundsLimits
