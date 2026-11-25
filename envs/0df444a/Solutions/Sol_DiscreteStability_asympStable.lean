-- Prove2me | solution 1 for DiscreteStability.asympStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:11.719345+00:00
-- url     : https://prove2.me/submissions/68bacae7-8589-4eba-8c8c-d3d772cf37d1

import Definitions.Def_DiscreteStability_Ascent
import Definitions.Def_DiscreteStability_Stability
import Theorems.Thm_DiscreteStability_asympStable_weighted

set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
open DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {xbar : E} {r₀ L Λ : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
variable [FiniteDimensional ℝ E]
namespace DiscreteStability
theorem _root_.solution (hH : LocalHyp f g xbar r₀ L) (hP : ∀ k, StepBound (P k) (lo k) (hi k))
    (hΛ : ∀ k, hi k ≤ Λ) {η : ℝ} (hη : 0 < η) (hS2 : L * Λ ≤ 2 - η)
    (hH1 : IsolatedMax f xbar) (hH2 : IsolatedCrit g xbar)
    (hH3 : Tendsto (fun N => ∑ k ∈ Finset.range N, lo k) atTop atTop) :
    UniformlyAsympStable P g xbar := by
  have hL := hH.L_nonneg
  apply asympStable_weighted hH hP hΛ (by linarith) hH1 hH2
  have h1 : Tendsto (fun N => η * ∑ k ∈ Finset.range N, lo k) atTop atTop :=
    hH3.const_mul_atTop hη
  refine tendsto_atTop_mono (fun N => ?_) h1
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have : L * hi k ≤ 2 - η := (mul_le_mul_of_nonneg_left (hΛ k) hL).trans hS2
  nlinarith [(hP k).lo_nonneg]
end DiscreteStability
