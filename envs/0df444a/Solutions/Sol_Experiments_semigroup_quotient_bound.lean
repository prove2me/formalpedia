-- Prove2me | solution 1 for Experiments.semigroup_quotient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:08.235277+00:00
-- url     : https://prove2.me/submissions/37b189b4-4565-4429-8f38-fd3d0c5f7f2c

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
import Theorems.Thm_Experiments_semigroup_nat_mul
import Theorems.Thm_Experiments_geometric_average_near_one
import Theorems.Thm_Experiments_geometric_quotient_bound

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
namespace Experiments
theorem _root_.solution (M : ℝ → A) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t)
    {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ s ∈ Set.Icc 0 δ, ‖M s - 1‖ ≤ (1 / 2 : ℝ))
    {n : ℕ} (hn : 0 < n) :
    ‖(n : ℝ) • (M (δ / n) - 1)‖ ≤ 2 * ‖M δ - 1‖ := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : 0 ≤ δ / (n : ℝ) := div_nonneg hδ.le (Nat.cast_nonneg n)
  have hnh : (n : ℝ) * (δ / n) = δ := mul_div_cancel₀ δ hn'
  have hp := semigroup_nat_mul M h0 hadd hh
  have hsteps : ∀ k ∈ Finset.range n, ‖M (δ / n) ^ k - 1‖ ≤ (1 / 2 : ℝ) := by
    intro k hk
    rw [← hp k]
    apply hnear
    refine ⟨mul_nonneg (Nat.cast_nonneg k) hh, ?_⟩
    calc
      _ ≤ (n : ℝ) * (δ / n) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk).le) hh
      _ = δ := hnh
  have hb := geometric_quotient_bound (M (δ / n)) hn
    (geometric_average_near_one (M (δ / n)) hn hsteps)
  simpa only [← hp n, hnh] using hb
end Experiments
