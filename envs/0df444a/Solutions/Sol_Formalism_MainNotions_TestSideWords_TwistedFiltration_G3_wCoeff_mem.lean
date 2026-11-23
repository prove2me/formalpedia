-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.wCoeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:41.093809+00:00
-- url     : https://prove2.me/submissions/88b8d337-16f2-4dfa-baea-43afafa23910

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_coeff_wCoeff

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
theorem _root_.solution {Fl : Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_Fil R} (w : Set ι) (M : ι × Fin n →₀ ℕ) {t : ℤ}
    {P : MvPolynomial (ι × Fin n) R} (hP : P ∈ (Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lift Fl 0).F t) :
    wCoeff w M P ∈ (Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_lift Fl 0).F t := by
  intro ν
  rw [coeff_wCoeff]
  split_ifs
  · simpa using hP (M + ν)
  · exact (Fl.F _).zero_mem
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
