-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_C_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:24.409181+00:00
-- url     : https://prove2.me/submissions/eeda4af6-4d13-4c28-99ce-e9a5dba9eb58

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_monomial_mem

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
    {a : B} (ha : a ∈ Fl.F t) : (C a : MvPolynomial σ B) ∈ (flt_lift Fl wt).F t := by
  have := flt_monomial_mem (wt := wt) (m := 0) (a := a) (t := t) (by simpa using ha)
  rwa [← C_apply] at this
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
