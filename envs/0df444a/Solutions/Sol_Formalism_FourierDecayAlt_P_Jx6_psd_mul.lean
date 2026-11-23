-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.psd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:44.632356+00:00
-- url     : https://prove2.me/submissions/4eac000d-2b30-4da3-a7d1-a36d941e1f3b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6
namespace Formalism.FourierDecayAlt.P.Jx6
theorem _root_.solution {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : TB.PSDOn F (fun x y => k x y * k' x y) := by
  unfold TB.PSDOn at *
  exact hk.hadamard hk'
end Formalism.FourierDecayAlt.P.Jx6
