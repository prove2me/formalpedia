-- Prove2me | solution 1 for Experiments.exists_bounded_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:20:59.409774+00:00
-- url     : https://prove2.me/submissions/ce60ec28-e555-4721-9619-0844ecba241c

import Mathlib
import Definitions.Def_Experiments_GeneratorBound
import Theorems.Thm_Experiments_semigroup_quotient_bound

set_option autoImplicit true
open Filter Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
namespace Experiments
theorem _root_.solution (M : ℝ → A)
    (hcont : ContinuousWithinAt M (Set.Ici 0) 0) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ δ > 0, ∃ C : ℝ, ∀ n : ℕ,
      ‖(δ / (n + 1 : ℝ))⁻¹ • (M (δ / (n + 1 : ℝ)) - 1)‖ ≤ C := by
  obtain ⟨r, hr, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp hcont (1 / 2) (by norm_num)
  let δ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnear : ∀ s ∈ Set.Icc 0 δ, ‖M s - 1‖ ≤ (1 / 2 : ℝ) := by
    intro s hs
    have hs' : dist s 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      dsimp [δ] at hs
      linarith [hs.2]
    simpa [dist_eq_norm, h0] using (hclose hs.1 hs').le
  refine ⟨δ, hδ, δ⁻¹ * (2 * ‖M δ - 1‖), ?_⟩
  intro n
  rw [inv_div, div_eq_inv_mul, mul_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hδ)]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  simpa only [Nat.cast_add_one] using
    semigroup_quotient_bound M h0 hadd hδ hnear (Nat.succ_pos n)
end Experiments
