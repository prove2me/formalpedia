-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.sum_inv_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:07.35447+00:00
-- url     : https://prove2.me/submissions/118f874a-dc7f-4924-a3dc-a88c6b96735c

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
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
namespace FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
private theorem oddLevels_subset_image_two_mul_add_one :
    oddLevels d ⊆ (Finset.range d).image (fun k => 2 * k + 1) := by
  intro i hi
  have hlt := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
  obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hi).2
  exact Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩
end FlowDualityReindexing
open FlowDualityReindexing
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowDualityReindexing
theorem _root_.solution (hl : 3 ≤ l) : ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹ ≤ gam l := by
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hq0 : (0 : ℝ) ≤ ((l : ℝ) ^ 2)⁻¹ := by positivity
  have hq1 : ((l : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h2 : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - ((l : ℝ) ^ 2)⁻¹ ≠ 0 := by linarith
  calc ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹
        ≤ ∑ i ∈ (Finset.range d).image (fun k => 2 * k + 1), ((l : ℝ) ^ i)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg oddLevels_subset_image_two_mul_add_one
            (fun i _ _ => by positivity)
      _ = ∑ k ∈ Finset.range d, ((l : ℝ) ^ (2 * k + 1))⁻¹ := by
          refine Finset.sum_image ?_
          intro a _ b _ h
          have : 2 * a + 1 = 2 * b + 1 := h
          omega
      _ = ∑ k ∈ Finset.range d, (l : ℝ)⁻¹ * (((l : ℝ) ^ 2)⁻¹) ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [pow_succ, pow_mul, mul_inv, inv_pow, mul_comm]
      _ = (l : ℝ)⁻¹ * ∑ k ∈ Finset.range d, (((l : ℝ) ^ 2)⁻¹) ^ k := by rw [Finset.mul_sum]
      _ ≤ (l : ℝ)⁻¹ * (1 / (1 - ((l : ℝ) ^ 2)⁻¹)) := by
          gcongr
          have := geom_sum_Ico_le_of_lt_one (m := 0) (n := d) hq0 hq1
          simpa using this
      _ = Formalism.IncomingBounds.gam l := by
          unfold Formalism.IncomingBounds.gam
          field_simp
end Formalism.IncomingBounds.FlowDualityReindexing
