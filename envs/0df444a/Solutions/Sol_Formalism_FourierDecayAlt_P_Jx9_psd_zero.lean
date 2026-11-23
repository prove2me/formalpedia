-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx9.psd_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:59.235122+00:00
-- url     : https://prove2.me/submissions/b2cac80a-9e53-4317-ab84-ae860fc51a04

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
variable {α X : Type}
namespace Formalism.FourierDecayAlt.P.Jx9
theorem _root_.solution (F : Finset α) : A5.IsPSD F (fun _ _ => (0 : ℂ)) := by
  intro a; simp
end Formalism.FourierDecayAlt.P.Jx9
