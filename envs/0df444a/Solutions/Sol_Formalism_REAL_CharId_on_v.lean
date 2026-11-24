-- Prove2me | solution 1 for Formalism.REAL.CharId_on_v
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:28.659196+00:00
-- url     : https://prove2.me/submissions/d1f5f3e7-45d1-45a8-8ec3-e11ccbabb0e7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_Mpow
import Theorems.Thm_Formalism_REAL_CharId_F_gen
import Theorems.Thm_Formalism_REAL_CharId_kill
import Theorems.Thm_Formalism_REAL_CharId_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℂ) (v : V)
    (hv : IsHW E ν v) (a b : Fin n) :
    ∑ i ∈ range (n + 1),
      (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a b v = 0 := by
  have hy : (Pi.single b v : Fin n → V) ∈ CharId_F E v 0 := CharId_F_gen E v 0 b (Nat.zero_le _)
  have hk := CharId_kill E hE ν v hv n 0 (by omega) (∏ s : Fin n, (X - C (lsh ν s))) (by simp) _ hy
  have hdeg : (∏ s : Fin n, (X - C (lsh ν s))).natDegree < n + 1 := by
    rw [natDegree_finset_prod_X_sub_C_eq_card]
    simp
  rw [aeval_eq_sum_range' hdeg] at hk
  have h := congrFun hk a
  simpa [LinearMap.sum_apply, Finset.sum_apply, CharId_Mpow, CharId_single] using h
end Formalism.REAL
