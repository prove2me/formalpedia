-- Prove2me | solution 1 for GabayMercier.DualAlgorithm.eq_3_23
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:28:08.952306+00:00
-- url     : https://prove2.me/submissions/aa475fe2-3626-484f-9537-0fa06532df98

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

open Filter Topology in
theorem solution (a b : ℝ) (u w : ℕ → ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hb : 0 < b)
    (hw : ∀ n, 0 ≤ w n) (hws : Summable w) (hu₀ : 0 ≤ u 0)
    (hrec : ∀ n, u (n + 1) = a * u n + b * w n) :
    Summable u ∧ Tendsto u atTop (𝓝 0) := by
  have hnn : ∀ n, 0 ≤ u n := by
    intro n
    induction n with
    | zero => exact hu₀
    | succ n ih =>
      rw [hrec]
      exact add_nonneg (mul_nonneg ha₀ ih) (mul_nonneg hb.le (hw n))
  have hsum : Summable u := by
    refine summable_of_sum_range_le (c := (u 0 + b * ∑' n, w n) / (1 - a)) hnn ?_
    intro N
    have h1 : ∑ i ∈ Finset.range (N + 1), u i
        = u 0 + (a * ∑ i ∈ Finset.range N, u i + b * ∑ i ∈ Finset.range N, w i) := by
      rw [Finset.sum_range_succ', add_comm]
      congr 1
      simp only [hrec, Finset.sum_add_distrib, Finset.mul_sum]
    have h2 : ∑ i ∈ Finset.range (N + 1), u i = ∑ i ∈ Finset.range N, u i + u N :=
      Finset.sum_range_succ _ _
    have h3 : ∑ i ∈ Finset.range N, w i ≤ ∑' n, w n :=
      hws.sum_le_tsum _ (fun i _ => hw i)
    have h4 := hnn N
    have h5 : (1 - a) * ∑ i ∈ Finset.range N, u i ≤ u 0 + b * ∑' n, w n := by
      nlinarith [mul_le_mul_of_nonneg_left h3 hb.le]
    rw [le_div_iff₀ (by linarith)]
    linarith
  exact ⟨hsum, hsum.tendsto_atTop_zero⟩
