-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.ctr_partial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:21.334846+00:00
-- url     : https://prove2.me/submissions/01fbd3b5-7f9a-4c7a-b3f1-a113bf7ce8cc

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctrF_pow_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_ctr_h_pow
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harmonicCoeff_recurrence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) (N : ℕ)
    (hN : N ≤ min A B) :
    ctrF K k (∑ l ∈ range (N + 1), cP K (A + B + k - 2) l • (hXY K k ^ l * (ctrF K k ^ l) f)) =
      cP K (A + B + k - 2) N • (hXY K k ^ N * (ctrF K k ^ (N + 1)) f) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := min_le_left A B
    have h2 := min_le_right A B
    have e1 : ctrF K k ((ctrF K k ^ (N + 1)) f) = (ctrF K k ^ (N + 1 + 1)) f := by
      rw [pow_succ' (ctrF K k) (N + 1), Module.End.mul_apply]
    have hc : (N + 1) * (A - (N + 1) + (B - (N + 1)) + k + N) = (N + 1) * (A + B + k - 2 - N) := by
      congr 1
      omega
    have hrec := harmonicCoeff_recurrence (K := K) (M := A + B + k - 2) (N := N) (by omega)
    rw [Finset.sum_range_succ, map_add, ih (by omega), map_smul,
      ctr_h_pow N (ctrF_pow_mem (N + 1) hf), e1, hc, smul_add, smul_smul, add_left_comm, ← add_smul,
      hrec, zero_smul, add_zero]
end Formalism.CountingSumsFrames.Har2
