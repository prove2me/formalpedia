-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_divDer_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:13.700921+00:00
-- url     : https://prove2.me/submissions/08af1d14-cb0a-4975-8ecb-dd1448e43a81

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_tay_coeff
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_Th_twist
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_Th_mem
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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) {t : ℤ} {F : MvPolynomial (ι × Fin n) R}
    (hF : twistSub LL S j F ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) (be : ι × Fin n →₀ ℕ) :
    twistSub LL S j (divDer be F) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (t - flt_cost LL S (!bm) be) := by
  have h1 := flt_lift_mem.1 (flt_Th_mem LL S j h hF) be
  have e1 : twistSub LL S j (divDer be F) = coeff be (flt_Th LL S j (twistSub LL S j F)) := by
    have h2 := congrArg (fun φ => coeff be (φ F)) (flt_Th_twist (R := R) LL S j)
    simp only [RingHom.comp_apply, coeff_map] at h2
    rw [← h2, flt_tay_coeff]
  rw [e1]
  exact h1
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
