-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.mp_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:52.106536+00:00
-- url     : https://prove2.me/submissions/98b0519d-af8d-48ea-8fa5-acf020e30a69

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
theorem _root_.solution (β : ℂ) (m : ℕ) : MeasurePreserving (split m) (muPi β (Tgt m)) (muRed β m) := by
  have := Formalism.FourierDecayAlt.P.G5.sigmaFinite_mu β
  have h3 := measurePreserving_sumPiEquivProdPi (X := fun _ : UT (m + 1) ⊕ Fin (m + 1) => ℂ)
    (fun _ => mu β)
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin m ⊕ (UT (m + 1) ⊕ Fin (m + 1)) => ℂ)
    (fun _ => mu β)
  have h1 := measurePreserving_sumPiEquivProdPi (X := fun _ : Tgt m => ℂ) (fun _ => mu β)
  have hu := measurePreserving_funUnique (mu β) Unit
  have key := (hu.prod ((MeasurePreserving.id _).prod h3 |>.comp h2)).comp h1
  convert key using 1 <;> rfl
end Formalism.FourierDecayAlt.P.WeakApproximationGL
