-- Prove2me | solution 1 for Formalism.UG.P.hermitian_correspondence_surjective_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:53.786016+00:00
-- url     : https://prove2.me/submissions/7e5dde8d-64b2-4ffc-9084-ce644a161f52

import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HermBridgeSurj := by
  intro K _ _ n _ _ h u _
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).symm u), ?_⟩
  unfold Formalism.UG.glEquiv
  simp
end Formalism.UG.P
