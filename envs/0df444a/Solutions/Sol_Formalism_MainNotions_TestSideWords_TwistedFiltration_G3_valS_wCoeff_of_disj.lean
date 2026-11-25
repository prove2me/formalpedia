-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.valS_wCoeff_of_disj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:59:36.45483+00:00
-- url     : https://prove2.me/submissions/6860c03e-052b-4335-ab82-1e1b20bbefdb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_wCoeff_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_twistSub_wCoeff
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_le_valS
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_withTop_le


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
theorem _root_.solution (w : Set ι) (hd : Disjoint S w) (F : MvPolynomial (ι × Fin n) R) (M : ι × Fin n →₀ ℕ) :
    valS LL S F ≤ valS LL S (wCoeff w M F) := by
  have h := Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_withTop_le (a := valS LL S F) (b := valS LL S (wCoeff w M F)) (N := 0) (by
    intro t ht
    rw [sub_zero, Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_le_valS] at *
    rw [twistSub_wCoeff LL S w hd]
    exact wCoeff_mem w M ht)
  simpa using h
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
