-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.product_of_energies
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:47:42.014566+00:00
-- url     : https://prove2.me/submissions/2e4845a5-fc9a-46db-82a4-a618616903a1

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Jx6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.J.ProductOfE := by
  intro r e sd h0 h1
  rw [Finset.prod_Icc_succ_top (by omega), h1, Finset.prod_eq_one, one_mul]
  intro i hi; rw [h0 i hi, add_zero]
end Formalism.FourierDecayAlt.P
