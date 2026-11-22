-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.psd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:41:56.756292+00:00
-- url     : https://prove2.me/submissions/1f406680-2d91-437c-af95-5962a3d13ca7

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix
variable {α : Type} {F : Finset α}
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution {k k' : α → α → ℂ} (hk : TB.PSDOn F k) (hk' : TB.PSDOn F k') :
    TB.PSDOn F (fun x y => k x y + k' x y) := by
  unfold TB.PSDOn at *
  exact hk.add hk'
end Formalism.FourierDecayAlt.P.Jx7
