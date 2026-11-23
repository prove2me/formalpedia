-- Prove2me | solution 1 for Experiments.exists_eq_exp_of_semigroup_finiteDifference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:23:12.451329+00:00
-- url     : https://prove2.me/submissions/f6ad7834-db3d-4da1-b3f0-30328f9932f9

import Definitions.Def_Experiments_GeneratorBound
import Definitions.Def_Experiments_FiniteDifferenceSemigroup
import Theorems.Thm_Experiments_eq_exp_of_sequence_generator
import Theorems.Thm_Experiments_exists_bounded_generators


set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
namespace Experiments
theorem _root_.solution [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by
  obtain ⟨δ, hδ, C, hbound⟩ := exists_bounded_generators M (hcont 0 (by simp)) h0 hadd
  let q : ℕ → A := fun n => (δ / (n + 1 : ℝ))⁻¹ • (M (δ / (n + 1 : ℝ)) - 1)
  obtain ⟨a, _, s, hs, hlim⟩ :=
    (isCompact_closedBall (0 : A) C).tendsto_subseq
      (x := q) (fun n => by simpa [Metric.mem_closedBall, dist_eq_norm, q] using hbound n)
  let h : ℕ → ℝ := fun n => δ / (s n + 1 : ℝ)
  have hpos : ∀ n, 0 < h n := fun n => div_pos hδ (by positivity)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (s n + 1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add_one] using
      hnat.comp ((tendsto_add_atTop_nat 1).comp hs.tendsto_atTop)
  have hz : Tendsto h atTop (𝓝 0) := by
    simpa only [h, Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hden).const_mul δ
  exact ⟨a, eq_exp_of_sequence_generator M hcont h0 hadd a h hpos hz hlim⟩
end Experiments
