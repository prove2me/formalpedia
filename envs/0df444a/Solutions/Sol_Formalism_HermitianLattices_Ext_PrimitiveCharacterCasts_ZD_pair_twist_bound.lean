-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.pair_twist_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.129196+00:00
-- url     : https://prove2.me/submissions/e2a6ba89-7242-4fd9-8d42-6bb3eab5fbe1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZTwist
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_neg_le_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_norm_cpow_step_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : PairTwistOf := by
  intro hPS p p' hp hp' hne w hw U hU
  set m : ℝ := (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) with hm
  set g : ℕ → ℂ := fun n => cv p n * (starRingEnd ℂ) (cv p' n) with hg
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-w) with hf
  have hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m := fun k => hPS p p' hp hp' hne k
  have hm0 : 0 ≤ m := by positivity
  have hrw : ∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), f n • g n := by
    refine sum_congr rfl (fun n _ => ?_); simp only [hf, hg, smul_eq_mul]; ring
  rw [hrw, Finset.sum_Ioc_by_parts f g (by omega : U < 2 * U)]
  have hb1 : ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (2 * U)‖ * ‖∑ i ∈ range (2 * U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb2 : ‖f (U + 1) • ∑ i ∈ range (U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (U + 1)‖ * ‖∑ i ∈ range (U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_cpow_neg_le_one (by omega) hw.le) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb3 : ‖∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ m * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ioc U (2 * U - 1),
        ‖(f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ ‖w‖ / U * m := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have hi' : U ≤ i := by have := (mem_Ioc.1 hi).1; omega
      exact mul_le_mul (norm_cpow_step_le hU hi' hw) (hGs _) (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hcnt : ((2 * U - 1 - U : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : 2 * U - 1 - U ≤ U)
    calc ((2 * U - 1 - U : ℕ) : ℝ) * (‖w‖ / U * m) ≤ U * (‖w‖ / U * m) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = m * ‖w‖ := by field_simp
  calc ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i - f (U + 1) • ∑ i ∈ range (U + 1), g i -
        ∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖
      ≤ m + m + m * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ ≤ 2 * m * (1 + ‖w‖) := by nlinarith [norm_nonneg w]
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
