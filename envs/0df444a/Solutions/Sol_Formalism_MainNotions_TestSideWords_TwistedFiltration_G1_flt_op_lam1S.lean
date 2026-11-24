-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_lam1S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:28.449117+00:00
-- url     : https://prove2.me/submissions/ed639aac-38e7-47a7-b5d7-14e38fa2a981

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_mem_lam
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lam1S_le


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
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (al be : ι × Fin n →₀ ℕ) (N : ℕ)
    (hN : vecDeg LL S al + covDeg LL S be ≤ N) :
    lam1S LL S (monomial al 1 * divDer be F) ≤ lam1S LL S F + ((N : ℤ) : WithBot ℤ) := by
  by_contra hcon
  push_neg at hcon
  cases hv : lam1S LL S (monomial al 1 * divDer be F) with
  | bot =>
    rw [hv] at hcon
    simp at hcon
  | coe w =>
    rw [hv] at hcon
    have hM : lam1S LL S F ≤ ((w - N - 1 : ℤ) : WithBot ℤ) := by
      cases hF : lam1S LL S F with
      | bot => exact bot_le
      | coe x =>
        rw [hF] at hcon
        norm_cast at hcon ⊢ <;> omega
    have hm := flt_op_mem_lam LL S hM al be N hN
    rw [← flt_lam1S_le, hv] at hm
    norm_cast at hm <;> omega
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
