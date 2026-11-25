-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.coeff_extract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:10:43.179353+00:00
-- url     : https://prove2.me/submissions/d8f2fe63-cf78-43a5-a0de-fa06e4f3db98

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) (a μ : ι → K) (c : ι) (hac : a c = 0) (ha : ∀ c', c' ≠ c → a c' ≠ 0)
    (h : ∀ t : ℕ, aeval B (∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c')))) *ᵥ w = 0) :
    B *ᵥ w = μ c • w := by
  set R : K[X][X] := ∏ c', (Polynomial.C (Polynomial.C (a c')) + X * Polynomial.C (X - Polynomial.C (μ c'))) with hR
  have hev : ∀ t : ℕ, R.eval (Polynomial.C (t : K)) =
      ∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c'))) := by
    intro t
    rw [hR, eval_prod]
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, eval_C]
  have hcoord : ∀ i, (aeval B (R.coeff 1) *ᵥ w) i = 0 := by
    intro i
    set q : K[X] := ∑ k ∈ Finset.range (R.natDegree + 2), monomial k ((aeval B (R.coeff k) *ᵥ w) i) with hq
    have hroot : ∀ t : ℕ, q.eval (t : K) = 0 := by
      intro t
      have h1 := congrFun (h t) i
      rw [← hev t, eval_eq_sum_range' (n := R.natDegree + 2) (by omega), map_sum, Matrix.sum_mulVec,
        Finset.sum_apply, Pi.zero_apply] at h1
      rw [hq, eval_finsetSum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
      rw [eval_monomial, ← map_pow, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    have hq0 : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))
      rintro _ ⟨t, rfl⟩
      exact hroot t
    have hc1 := congrArg (fun p => Polynomial.coeff p 1) hq0
    simp only [hq, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, coeff_zero] at hc1
    rw [if_pos (by omega)] at hc1
    exact hc1
  have hR1 : R.coeff 1 = (X - Polynomial.C (μ c)) * Polynomial.C (∏ c' ∈ Finset.univ.erase c, a c') := by
    rw [hR, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), hac, map_zero, map_zero, zero_add, mul_assoc]
    refine (coeff_X_mul _ 0).trans ?_
    rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero]
  have hπ : ∏ c' ∈ Finset.univ.erase c, a c' ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c' hc' => ha c' (Finset.ne_of_mem_erase hc')
  have hv : aeval B (R.coeff 1) *ᵥ w = 0 := funext hcoord
  rw [hR1, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, map_sub, aeval_X, aeval_C, Matrix.sub_mulVec,
    alg_mulVec1] at hv
  have h2 := (smul_eq_zero.1 hv).resolve_left hπ
  rwa [sub_eq_zero] at h2
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
