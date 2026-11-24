-- Prove2me | solution 1 for Formalism.GM.FrozenVariableLemmas.freeze_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:32.505431+00:00
-- url     : https://prove2.me/submissions/c54d5b4e-d463-438b-a765-dae43599b8c1

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_mul
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_X
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_pow
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_aeval
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableLemmas_snoc_vec_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
namespace Formalism.GM.FrozenVariableLemmas
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.IsFrozenInv p LL ρ n (M.freeze p LL ρ n f) := by
  intro c hc
  have hX := glAct_full_X p (LL.snoc n) c ρ
  have hlast : M.glAct p (LL.snoc n) (N + 1) c ρ (X (Fin.last N, ρ)) = 0 := by
    rw [hX, snoc_vec_last]
    simp [Ne.symm hc]
  have hsub : ∀ x, M.glAct p (LL.snoc n) (N + 1) c ρ (M.freezeSub p LL ρ x) = 0 := by
    rintro ⟨i, c'⟩
    simp only [M.freezeSub]
    by_cases hv : LL.vec i
    · by_cases hc' : c' = ρ
      · rw [if_pos hv, if_pos hc', _root_.map_sum]
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, if_true, Bool.false_eq_true,
          if_false, mul_ite, mul_zero, mul_neg, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ]
        ring
      · rw [if_pos hv, if_neg hc']
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
    · by_cases hc' : c' = ρ
      · rw [if_neg hv, if_pos hc']
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
      · rw [if_neg hv, if_neg hc', _root_.map_sub]
        simp only [glAct_full_mul, hX, snoc_vec_castSucc, snoc_vec_last, hv, hc', Ne.symm hc, if_true, if_false, Bool.false_eq_true, mul_zero, add_zero]
        by_cases hcc : c' = c
        · simp only [hcc, if_true]
          ring
        · simp only [hcc, if_false, mul_zero, sub_zero]
  unfold M.freeze
  rw [glAct_full_mul, glAct_full_pow _ _ _ _ _ hlast, glAct_full_aeval _ _ _ _ _ hsub, mul_zero, mul_zero,
    add_zero]
end Formalism.GM.FrozenVariableLemmas
