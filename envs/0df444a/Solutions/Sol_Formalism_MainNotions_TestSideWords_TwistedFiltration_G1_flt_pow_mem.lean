-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:08:26.566273+00:00
-- url     : https://prove2.me/submissions/d5d6756b-03a4-4050-a7b2-daa35fb02c7f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration

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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution {B : Type*} [CommRing B] (Fl : flt_Fil B) {t : ℤ} {a : B} (ha : a ∈ Fl.F t) (k : ℕ) :
    a ^ k ∈ Fl.F (k * t) := by
  induction k with
  | zero => simpa using Fl.one_mem
  | succ k ih =>
    rw [pow_succ]
    have := Fl.mul_mem ih ha
    have e : ((k : ℤ) * t + t) = ((k + 1 : ℕ) : ℤ) * t := by push_cast; ring
    rwa [e] at this
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
