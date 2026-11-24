-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.hook_product_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:10.782804+00:00
-- url     : https://prove2.me/submissions/74bd1e32-3ced-4d57-9996-cc4ea2f6c975

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_hook_den_bounds
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_fact_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution : HookProductBounds := by
  intro N nu hnu
  set D : ℝ := ∏ i : Fin (N+1), ∏ j ∈ univ.filter (fun j => i < j),
    (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) with hD
  set num : ℝ := ∏ i : Fin (N + 1), ((nu i + N - i : ℕ).factorial : ℝ) with hnum
  set Mr : ℝ := (nu 0 : ℝ) + N + 1 with hMr
  have hM1 : (1:ℝ) ≤ Mr := by
    have h0 : (0:ℝ) ≤ (nu 0 : ℝ) + N := by positivity
    linarith [hMr]
  have hH : hookF nu = num / D := by
    unfold hookF
    congr 1
  have hD1 : 1 ≤ D := by
    rw [hD]
    calc (1:ℝ) = ∏ _i : Fin (N+1), ∏ _j ∈ univ.filter (fun j => _i < j), (1:ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro i _
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro j hj
        exact (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).1
  have hDM : D ≤ Mr ^ ((N + 1) ^ 2) := by
    rw [hD]
    calc _ ≤ ∏ _i : Fin (N+1), Mr ^ (N + 1) := by
          apply Finset.prod_le_prod
          · intro i _
            apply Finset.prod_nonneg
            intro j hj
            exact zero_le_one.trans (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).1
          · intro i _
            calc _ ≤ ∏ _j ∈ univ.filter (fun j => i < j), Mr := by
                  apply Finset.prod_le_prod
                  · intro j hj
                    exact zero_le_one.trans (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).1
                  · intro j hj
                    exact (hook_den_bounds N nu hnu i j (mem_filter.mp hj).2).2
              _ = Mr ^ (univ.filter (fun j => i < j)).card := prod_const _
              _ ≤ Mr ^ (N + 1) := by
                  apply pow_le_pow_right₀ hM1
                  calc _ ≤ (univ : Finset (Fin (N+1))).card := card_filter_le _ _
                    _ = N + 1 := by simp
      _ = Mr ^ ((N + 1) ^ 2) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul, sq]
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hnum0 : 0 < num := by rw [hnum]; positivity
  have hnumM : num ≤ (∏ i : Fin (N + 1), ((nu i).factorial : ℝ)) * Mr ^ ((N + 1) ^ 2) := by
    rw [hnum]
    calc _ ≤ ∏ i : Fin (N + 1), (((nu i).factorial : ℝ) * Mr ^ (N + 1)) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro i _
          have := fact_bound (nu i) (nu 0) N i (hnu (Fin.zero_le i)) (Nat.lt_succ_iff.mp i.isLt)
          rw [hMr]
          exact_mod_cast this
      _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← pow_mul, sq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hH]
    exact div_le_self hnum0.le hD1
  · rw [hH, Real.log_div hnum0.ne' hD0.ne', hnum,
      Real.log_prod (fun i _ => by positivity)]
    have hl : Real.log D ≤ ((N:ℝ) + 1) ^ 2 * Real.log Mr := by
      calc Real.log D ≤ Real.log (Mr ^ ((N + 1) ^ 2)) := Real.log_le_log hD0 hDM
        _ = ((N:ℝ) + 1) ^ 2 * Real.log Mr := by rw [Real.log_pow]; push_cast; ring
    linarith
  · rw [hH]
    have hp : 0 < ∏ i : Fin (N + 1), ((nu i).factorial : ℝ) := by positivity
    rw [div_div, div_le_iff₀ (mul_pos hD0 hp)]
    calc num ≤ (∏ i : Fin (N + 1), ((nu i).factorial : ℝ)) * Mr ^ ((N + 1) ^ 2) := hnumM
      _ ≤ Mr ^ ((N + 1) ^ 2) * (D * ∏ i : Fin (N + 1), ((nu i).factorial : ℝ)) := by
        nlinarith [pow_pos (lt_of_lt_of_le zero_lt_one hM1) ((N+1)^2)]
end Formalism.LogVandermondeBounds.flipTwoThree
