-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_hom_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:34.801186+00:00
-- url     : https://prove2.me/submissions/6d7281af-01ca-4b25-b3d1-f4d0af8b83b3

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lift_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_hom_monomial

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
theorem _root_.solution {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl : flt_Fil B₀) (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hC : ∀ (t : ℤ) (b : B₀), b ∈ Fl.F t → φ (C b) ∈ Fl'.F t)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) {t : ℤ} {P : MvPolynomial σ B₀}
    (hP : P ∈ (flt_lift Fl wt).F t) : φ P ∈ Fl'.F t := by
  classical
  rw [P.as_sum, map_sum]
  refine (Fl'.F t).sum_mem fun m _ => ?_
  have e : monomial m (coeff m P) = C (coeff m P) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [e, map_mul]
  have := Fl'.mul_mem (hC _ _ ((flt_lift_mem.1 hP) m)) (flt_hom_monomial Fl' φ wt hX m)
  rwa [sub_add_cancel] at this
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
