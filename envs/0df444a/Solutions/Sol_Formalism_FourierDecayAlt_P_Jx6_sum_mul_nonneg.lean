-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.sum_mul_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:25.723074+00:00
-- url     : https://prove2.me/submissions/11f9b393-859e-4756-b000-095914637f9a

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_psd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx6_sum_nonneg_of_psd

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
    (hk' : TB.PSDOn F k') : 0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y * k' x y).re :=
  sum_nonneg_of_psd (psd_mul hk hk')
end Formalism.FourierDecayAlt.P.Jx6
