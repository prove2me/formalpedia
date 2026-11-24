-- Prove2me | solution 1 for Formalism.IncomingBounds.frobenius_orbit_sum_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:13.368393+00:00
-- url     : https://prove2.me/submissions/33a1e15b-19b7-4798-a44d-69c67b2fd8a3

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FrobOrbitPeriod
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
private lemma inv_pow_succ_mul (p : ℝ) (k n : ℕ) : (p ^ ((n + 1) * k))⁻¹ = ((p ^ k)⁻¹) ^ (n + 1) := by
  rw [mul_comm, pow_mul, inv_pow]
private lemma summable_inv_pow_mul_of_bounded (p : ℝ) (hp : 1 < p) (k : ℕ) (hk : 1 ≤ k) (b : ℕ → ℝ)
    (M : ℝ) (hb : ∀ n, |b n| ≤ M) : Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * b n) := by
  have hpk : 1 < p ^ k := one_lt_pow₀ hp (by omega)
  have hq0 : 0 ≤ (p ^ k)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p ^ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpk
  refine Summable.of_norm_bounded (g := fun n : ℕ => M * ((p ^ k)⁻¹ * ((p ^ k)⁻¹) ^ n))
    (((summable_geometric_of_lt_one hq0 hq1).mul_left _).mul_left _) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, inv_pow_succ_mul, abs_of_nonneg (pow_nonneg hq0 _), ← pow_succ',
    mul_comm M]
  exact mul_le_mul_of_nonneg_left (hb n) (pow_nonneg hq0 _)
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : FrobOrbitSum := by
  intro α _ φ p hp k hk a
  have hpk : 1 < p ^ k := one_lt_pow₀ hp (by omega)
  have hq0 : 0 ≤ (p ^ k)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (p ^ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpk
  have hs : ∀ τ : α, Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) := by
    intro τ
    refine summable_inv_pow_mul_of_bounded p hp k hk _ (∑ σ, |a σ|) (fun n => ?_)
    exact Finset.single_le_sum (f := fun σ => |a σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  rw [Finset.sum_sub_distrib, ← Summable.tsum_finsetSum (fun τ _ => hs τ)]
  have e : ∀ n : ℕ, ∑ τ : α, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ) =
      ((p ^ k)⁻¹) ^ (n + 1) * ∑ τ, a τ := by
    intro n
    rw [← Finset.mul_sum, Equiv.sum_comp (φ ^ (n + 1)) a, inv_pow_succ_mul]
  have hne : p ^ k - 1 ≠ 0 := (by linarith : (0 : ℝ) < p ^ k - 1).ne'
  have hne' : p ^ k ≠ 0 := (by linarith : (0 : ℝ) < p ^ k).ne'
  have hg : ∑' n : ℕ, ((p ^ k)⁻¹) ^ (n + 1) = 1 / (p ^ k - 1) := by
    rw [tsum_congr (fun n => pow_succ' ((p ^ k)⁻¹) n), tsum_mul_left,
      tsum_geometric_of_lt_one hq0 hq1]
    field_simp
  rw [tsum_congr e, tsum_mul_right, hg, ← Finset.sum_div]
  ring
end Formalism.IncomingBounds
