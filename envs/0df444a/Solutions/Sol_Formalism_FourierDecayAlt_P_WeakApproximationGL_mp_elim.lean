-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.mp_elim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:51.334992+00:00
-- url     : https://prove2.me/submissions/089d2ee1-cbc3-42e7-a592-6a7621357725

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
theorem _root_.solution (β : ℂ) (m : ℕ) :
    MeasurePreserving (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) (muXY β m) (muPi β (FinalTheorems m)) := by
  have := Formalism.FourierDecayAlt.P.G5.sigmaFinite_mu β
  have h := measurePreserving_sumPiEquivProdPi_symm (X := fun _ : FinalTheorems m => ℂ) (fun _ => mu β)
  have e : (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) =
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : FinalTheorems m => ℂ)).symm := by
    funext p i
    cases i <;> rfl
  rw [e]
  exact h
end Formalism.FourierDecayAlt.P.WeakApproximationGL
