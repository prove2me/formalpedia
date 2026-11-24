-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_op_valS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:32.913933+00:00
-- url     : https://prove2.me/submissions/7d8fa817-63ec-4a6b-a05b-ea4d3e7df3cc

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_mem_val
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_le_valS


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
    (hN : covDeg LL S al + vecDeg LL S be ≤ N) :
    valS LL S F ≤ valS LL S (monomial al 1 * divDer be F) + ((N : ℤ) : WithTop ℤ) := by
  by_contra hcon
  push_neg at hcon
  cases hv : valS LL S (monomial al 1 * divDer be F) with
  | top =>
    rw [hv] at hcon
    simp at hcon
  | coe w =>
    rw [hv] at hcon
    have ht : ((w + N + 1 : ℤ) : WithTop ℤ) ≤ valS LL S F := by
      cases hF : valS LL S F with
      | top => exact le_top
      | coe x =>
        rw [hF] at hcon
        norm_cast at hcon ⊢ <;> omega
    have hm := flt_op_mem_val LL S ht al be N hN
    rw [← flt_le_valS, hv] at hm
    norm_cast at hm <;> omega
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
