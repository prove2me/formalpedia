-- Prove2me | solution 1 for Erdos266.radius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:06:57.428381+00:00
-- url     : https://prove2.me/submissions/01844b88-8e41-4093-a54a-0f7554674e36

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_P2M_Erdos266__A_le_one_15aa108a0284
public import Theorems.Thm_Erdos266_bigM_le_sqrt
public import Theorems.Thm_Erdos266_one_le_bigN


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {k i : ℕ} (_hk : 2 ≤ k) :
    εA (dOf k) * bigM k / (bigN k : ℝ) ^ (i + 2) ≤ ((bigN k : ℝ))⁻¹ := by
  have hN1 : (1:ℝ) ≤ (bigN k : ℝ) := by exact_mod_cast one_le_bigN k
  have hN0 : (0:ℝ) < (bigN k : ℝ) := by linarith
  have hM : (bigM k : ℝ) ≤ (bigN k : ℝ) := by
    have h1 : bigM k ≤ bigN k :=
      le_trans (bigM_le_sqrt k) (Nat.sqrt_le_self _)
    exact_mod_cast h1
  have hpow : (bigN k : ℝ) ^ 2 ≤ (bigN k : ℝ) ^ (i + 2) :=
    pow_le_pow_right₀ hN1 (by omega)
  have hM0 : (0:ℝ) ≤ (bigM k : ℝ) := Nat.cast_nonneg _
  have h2 : εA (dOf k) * (bigM k : ℝ) ≤ (bigN k : ℝ) := by
    calc εA (dOf k) * (bigM k : ℝ) ≤ 1 * (bigM k : ℝ) :=
          mul_le_mul_of_nonneg_right (εA_le_one _) hM0
    _ = (bigM k : ℝ) := one_mul _
    _ ≤ (bigN k : ℝ) := hM
  rw [div_le_iff₀ (by positivity : (0:ℝ) < (bigN k : ℝ) ^ (i + 2)),
    inv_mul_eq_div, le_div_iff₀ hN0]
  calc εA (dOf k) * (bigM k : ℝ) * (bigN k : ℝ)
      ≤ (bigN k : ℝ) * (bigN k : ℝ) :=
        mul_le_mul_of_nonneg_right h2 hN0.le
  _ = (bigN k : ℝ) ^ 2 := by ring
  _ ≤ (bigN k : ℝ) ^ (i + 2) := hpow
end Erdos266
