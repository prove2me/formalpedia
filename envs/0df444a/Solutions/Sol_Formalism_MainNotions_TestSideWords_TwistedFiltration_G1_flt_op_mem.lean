-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:25.249026+00:00
-- url     : https://prove2.me/submissions/486c0e3e-740f-49ad-9580-8ede392fd9ea

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_divDer_mem
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_twist_monomial_mem


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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (al be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al 1 * divDer be F) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F (t - (flt_cost LL S bm al + flt_cost LL S (!bm) be)) := by
  rw [map_mul]
  have h1 := flt_twist_monomial_mem (R := R) LL S j h al
  have h2 := flt_divDer_mem LL S j h hF be
  have h3 := (laurentCoeffFiltration R n (ι × Fin n) e).mul_mem h1 h2
  rwa [show -flt_cost LL S bm al + (t - flt_cost LL S (!bm) be) =
    t - (flt_cost LL S bm al + flt_cost LL S (!bm) be) by ring] at h3
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
