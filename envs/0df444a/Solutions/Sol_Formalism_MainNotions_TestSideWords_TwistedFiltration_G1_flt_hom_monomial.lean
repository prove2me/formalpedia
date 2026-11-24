-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_hom_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:21.860876+00:00
-- url     : https://prove2.me/submissions/91a15793-cf17-4994-89b2-234d7671ebce

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TMemLaurentFiltration
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_pow_mem

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
theorem _root_.solution {B₀ B' : Type*} [CommRing B₀] [CommRing B'] {σ : Type*} (Fl' : flt_Fil B')
    (φ : MvPolynomial σ B₀ →+* B') (wt : (σ →₀ ℕ) →+ ℤ)
    (hX : ∀ w, φ (X w) ∈ Fl'.F (wt (Finsupp.single w 1))) (m : σ →₀ ℕ) :
    φ (monomial m 1) ∈ Fl'.F (wt m) := by
  classical
  refine Finsupp.induction m ?_ ?_
  · simpa using Fl'.one_mem
  · intro a b f _ _ ih
    have e : monomial (Finsupp.single a b + f) (1 : B₀) = monomial (Finsupp.single a b) 1 * monomial f 1 := by
      rw [monomial_mul, one_mul]
    rw [e, ← X_pow_eq_monomial, map_mul, map_pow, map_add]
    refine Fl'.mul_mem ?_ ih
    have hp := flt_pow_mem Fl' (hX a) b
    have e2 : Finsupp.single a b = b • Finsupp.single a 1 := by simp
    rw [e2, map_nsmul, nsmul_eq_mul]
    exact hp
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
