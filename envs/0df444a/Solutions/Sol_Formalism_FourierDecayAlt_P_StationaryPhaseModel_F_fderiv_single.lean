-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_fderiv_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:00.680893+00:00
-- url     : https://prove2.me/submissions/63b2f394-e603-48a7-b5b5-ecc89bc9c1e8

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {d : ℕ} {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} {k : Fin d} {D : ℂ}
    (hg : DifferentiableAt ℂ g x) (h : HasDerivAt (fun ξ => g (Function.update x k ξ)) D (x k)) :
    fderiv ℂ g x (Pi.single k 1) = D := by
  have h1 : HasDerivAt (fun ξ => Function.update x k ξ) (Pi.single k (1:ℂ)) (x k) := hasDerivAt_update x k (x k)
  have h2 : HasFDerivAt g (fderiv ℂ g x) (Function.update x k (x k)) := by
    rw [Function.update_eq_self]; exact hg.hasFDerivAt
  exact (h2.comp_hasDerivAt (x k) h1).unique h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
