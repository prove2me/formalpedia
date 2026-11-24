-- Prove2me | solution 1 for Formalism.IncomingBounds.frobenius_orbit_period_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:13.038436+00:00
-- url     : https://prove2.me/submissions/cda5ef20-9a52-4c89-90a1-72f3723c5681

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
private lemma pow_mul_apply_eq_self {α : Type} (φ : Equiv.Perm α) (τ : α) (f : ℕ)
    (hf : (φ ^ f) τ = τ) : ∀ q : ℕ, (φ ^ (f * q)) τ = τ := by
  intro q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, pow_add φ (f * q) f, Equiv.Perm.mul_apply, hf, ih]
private lemma pow_apply_eq_pow_mod_apply {α : Type} (φ : Equiv.Perm α) (τ : α) (f : ℕ)
    (hf : (φ ^ f) τ = τ) (m : ℕ) : (φ ^ m) τ = (φ ^ (m % f)) τ := by
  conv_lhs => rw [← Nat.mod_add_div m f]
  rw [pow_add φ (m % f) (f * (m / f)), Equiv.Perm.mul_apply, pow_mul_apply_eq_self φ τ f hf]
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : FrobOrbitPeriod := by
  intro α φ p hp k hk a τ f hf hfix
  set c : ℕ → ℝ := fun n => (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ) with hc
  show ∑' n, c n = (∑ n ∈ Finset.range f, c n) / (1 - (p ^ (f * k))⁻¹)
  have hbd : ∀ n, |a ((φ ^ (n + 1)) τ)| ≤ ∑ r ∈ Finset.range f, |a ((φ ^ r) τ)| := by
    intro n
    rw [pow_apply_eq_pow_mod_apply φ τ f hfix (n + 1)]
    exact Finset.single_le_sum (f := fun r => |a ((φ ^ r) τ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
  have hs : Summable c := summable_inv_pow_mul_of_bounded p hp k hk _ _ hbd
  have hshift : ∀ n, c (n + f) = (p ^ (f * k))⁻¹ * c n := by
    intro n
    simp only [hc]
    have e1 : (φ ^ (n + f + 1)) τ = (φ ^ (n + 1)) τ := by
      rw [show n + f + 1 = (n + 1) + f by omega, pow_add φ (n + 1) f, Equiv.Perm.mul_apply, hfix]
    rw [e1, show (n + f + 1) * k = (n + 1) * k + f * k by ring, pow_add p ((n + 1) * k) (f * k),
      mul_inv]
    ring
  have htail : ∑' i, c (i + f) = (p ^ (f * k))⁻¹ * ∑' i, c i := by
    rw [← tsum_mul_left]; exact tsum_congr hshift
  have hsplit := hs.sum_add_tsum_nat_add f
  rw [htail] at hsplit
  have hpf : 1 < p ^ (f * k) := one_lt_pow₀ hp (Nat.mul_ne_zero (by omega) (by omega))
  have hq : (p ^ (f * k))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpf
  have hne : 1 - (p ^ (f * k))⁻¹ ≠ 0 := (by linarith : (0 : ℝ) < 1 - (p ^ (f * k))⁻¹).ne'
  rw [eq_div_iff hne]
  linear_combination -hsplit
end Formalism.IncomingBounds
