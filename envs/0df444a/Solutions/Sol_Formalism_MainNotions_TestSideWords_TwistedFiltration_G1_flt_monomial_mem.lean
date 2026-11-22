-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_monomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:37.374773+00:00
-- url     : https://prove2.me/submissions/2da7002f-8391-484f-839a-837b225b3d32

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lift_mem

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
theorem _root_.solution {B : Type*} [CommRing B] {σ : Type*} {Fl : flt_Fil B} {wt : (σ →₀ ℕ) →+ ℤ} {t : ℤ}
    {m : σ →₀ ℕ} {a : B} (ha : a ∈ Fl.F (t - wt m)) : monomial m a ∈ (flt_lift Fl wt).F t := by
  classical
  rw [flt_lift_mem]
  intro m'
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact ha
  · exact (Fl.F _).zero_mem
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
