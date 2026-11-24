-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.map_algebraMap_smul_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:22.377298+00:00
-- url     : https://prove2.me/submissions/b44ec6c2-2c0b-449f-bbf3-c617bb28aa2b

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution (R O : Type) [CommRing R] [CommRing O] [Algebra R O] {σ : Type} (a : R)
    (f : MvPolynomial σ R) :
    map (algebraMap R O) (a • f) = algebraMap R O a • map (algebraMap R O) f := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, ← MvPolynomial.smul_eq_C_mul]
end Formalism.CohomologicalDescent.SL2BinomialLattices
