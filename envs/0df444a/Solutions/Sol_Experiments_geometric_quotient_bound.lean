-- Prove2me | solution 1 for Experiments.geometric_quotient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:01:27.227004+00:00
-- url     : https://prove2.me/submissions/b936a826-1f5a-49ae-9e18-962d16c8da6d

import Mathlib
import Definitions.Def_Experiments_GeneratorBound

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
namespace Experiments
theorem _root_.solution (x : A) {n : ℕ} (hn : 0 < n)
    (hx : ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k) - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(n : ℝ) • (x - 1)‖ ≤ 2 * ‖x ^ n - 1‖ := by
  let d := (n : ℝ) • (x - 1)
  let q := (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, x ^ k)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have htel : d * q = x ^ n - 1 := by
    dsimp [d, q]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hn',
      one_smul, mul_geom_sum]
  have hq : ‖1 - q‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_sub_rev]
    exact hx
  have hbound : ‖d‖ ≤ ‖x ^ n - 1‖ + ‖d‖ * (1 / 2 : ℝ) := by
    calc
      ‖d‖ = ‖d * q + d * (1 - q)‖ := by congr 1; noncomm_ring
      _ ≤ ‖d * q‖ + ‖d * (1 - q)‖ := norm_add_le _ _
      _ ≤ ‖x ^ n - 1‖ + ‖d‖ * ‖1 - q‖ := by
        rw [htel]
        exact add_le_add (le_refl _) (norm_mul_le d (1 - q))
      _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hq (norm_nonneg d))
  change ‖d‖ ≤ _
  linarith
end Experiments
