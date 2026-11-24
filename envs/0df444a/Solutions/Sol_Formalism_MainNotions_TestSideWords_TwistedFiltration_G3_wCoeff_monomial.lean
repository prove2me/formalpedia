-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.wCoeff_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:38.238839+00:00
-- url     : https://prove2.me/submissions/201e475b-17cd-4265-ab9e-b0fae8409e94

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wfree_monomial
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wCoeff_mul_monomial
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_monomial_split
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_filter_neg_filter_pos

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
theorem _root_.solution (w : Set ι) (M μ : ι × Fin n →₀ ℕ) (c : R) :
    wCoeff w M (monomial μ c) = if μ.filter (fun v => v.1 ∈ w) = M then monomial (μ.filter (fun v => v.1 ∉ w)) c else 0 := by
  rw [monomial_split w μ c, wCoeff_mul_monomial w M _ _ (wfree_monomial w μ c) (filter_neg_filter_pos w μ)]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
