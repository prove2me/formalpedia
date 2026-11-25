-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.kernel_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:33.408524+00:00
-- url     : https://prove2.me/submissions/0d198dd4-1994-4d17-be6a-9ef6f358e485

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AxiomsFromFamilies
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_tb_congr

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : KernelOfLocal := by
  intro hS hD α P _ Y K k a hK hk
  exact Jx9.tb_congr (fun x hx y hy => (hK x hx y hy).symm) (hD α Y _ a (hS α P Y k hk))
end Formalism.FourierDecayAlt.P
