-- Prove2me | solution 1 for Complex.exists_forall_norm_pow_sub_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T14:18:24.013674+00:00
-- url     : https://prove2.me/submissions/2c368a47-bac8-4705-81f5-6c442bba7c7e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.ProperSpace

namespace Complex
end Complex
namespace Filter
end Filter
namespace Finset
end Finset
namespace Topology
end Topology


/-!
# Bounding the terms of a family from bounds on its power sums

If `ω : ι → ℂ` is a finite family of complex numbers whose power sums satisfy
`‖∑ i, ω i ^ k‖ ≤ C * B ^ k` for every `k > 0`, then every `ω i` satisfies `‖ω i‖ ≤ B`.

This is the standard "no cancellation in the long run" argument: writing `M` for the largest
modulus occurring in the family and `S` for the set of indices attaining it, the numbers
`ω i / M` for `i ∈ S` lie on the unit circle, so by compactness of the torus there are
arbitrarily large exponents `n` for which all the `(ω i / M) ^ n`, `i ∈ S`, are simultaneously
close to `1`.  For such `n` the maximal terms of `∑ i, ω i ^ n` add up essentially without
cancellation, forcing `M ^ n ≲ C * B ^ n`, which is impossible for large `n` unless `M ≤ B`.
-/
set_option autoImplicit false
open Finset Filter Topology
open Complex

theorem solution {ι : Type*} [Fintype ι] {u : ι → ℂ}
    (hu : ∀ i, ‖u i‖ = 1) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < n ∧ ∀ i, ‖u i ^ n - 1‖ < ε := by
  set M : ℕ := N + 1 with hM
  set g : ℕ → (ι → ℂ) := fun j i => u i ^ (j * M) with hg
  have hnorm : ∀ j i, ‖g j i‖ = 1 := by
    intro j i
    simp [hg, norm_pow, hu i]
  have hmem : ∀ j, g j ∈ Metric.closedBall (0 : ι → ℂ) 1 := by
    intro j
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    exact le_of_eq (hnorm j i)
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ι → ℂ) 1).tendsto_subseq hmem
  have hcauchy : CauchySeq (g ∘ φ) := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨K, hK⟩ := hcauchy ε hε
  have hd : dist (g (φ (K + 1))) (g (φ K)) < ε := hK (K + 1) (Nat.le_succ K)
  set p := φ K with hp
  set q := φ (K + 1) with hq
  have hpq : p < q := hφ (Nat.lt_succ_self K)
  refine ⟨(q - p) * M, ?_, ?_, fun i => ?_⟩
  · calc N ≤ M := by omega
      _ = 1 * M := (one_mul M).symm
      _ ≤ (q - p) * M := Nat.mul_le_mul_right M (by omega)
  · exact Nat.mul_pos (by omega) (by omega)
  · have hsum : p * M + (q - p) * M = q * M := by
      rw [← Nat.add_mul]
      congr 1
      omega
    have key : u i ^ (p * M) * (u i ^ ((q - p) * M) - 1) = g q i - g p i := by
      rw [mul_sub, mul_one, ← pow_add, hsum]
    have : ‖u i ^ ((q - p) * M) - 1‖ = ‖g q i - g p i‖ := by
      rw [← key, norm_mul, norm_pow, hu i, one_pow, one_mul]
    rw [this]
    calc ‖g q i - g p i‖ = dist (g q i) (g p i) := (dist_eq_norm _ _).symm
      _ ≤ dist (g q) (g p) := dist_le_pi_dist _ _ i
      _ < ε := hd
