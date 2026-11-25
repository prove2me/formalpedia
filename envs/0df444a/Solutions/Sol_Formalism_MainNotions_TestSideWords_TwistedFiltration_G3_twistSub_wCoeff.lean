-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_wCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:34.674162+00:00
-- url     : https://prove2.me/submissions/9c0994fa-9458-4a6b-a3ab-a5a7553ad8b2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wCoeff_add
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wfree_monomial
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wCoeff_mul_monomial
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_monomial_split
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_filter_neg_filter_pos
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wCoeff_monomial
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_wfree
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_monomial_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution (w : Set ι) (hd : Disjoint S w) (j : Fin n) (M : ι × Fin n →₀ ℕ)
    (F : MvPolynomial (ι × Fin n) R) : twistSub LL S j (wCoeff w M F) = wCoeff w M (twistSub LL S j F) := by
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [wCoeff_add, map_add, map_add, wCoeff_add, hP, hQ]
  | monomial μ c =>
    rw [wCoeff_monomial, monomial_split w μ c, map_mul, twistSub_monomial_w LL S w hd j _ (filter_neg_filter_pos w μ),
      wCoeff_mul_monomial w M _ _ (twistSub_wfree LL S w j _ (wfree_monomial w μ c)) (filter_neg_filter_pos w μ)]
    split_ifs <;> simp
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
