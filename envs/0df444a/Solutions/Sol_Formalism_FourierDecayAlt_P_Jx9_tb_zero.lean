-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.tb_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:40.293908+00:00
-- url     : https://prove2.me/submissions/4523cc10-4dd1-451e-aeb0-488ef079ddca

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx9
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution {α : Type} {F : Finset α} : TB.PSDOn F (fun _ _ : α => (0 : ℂ)) := by
  unfold TB.PSDOn; exact Matrix.PosSemidef.zero
end Formalism.FourierDecayAlt.P.Jx9
