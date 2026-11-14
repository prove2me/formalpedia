-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:28.912208+00:00
-- url     : https://prove2.me/submissions/757f0285-9407-4609-994f-dfd7e4fb1d39

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains
import Theorems.Thm_ConsistentSubmodular_Chains_isEqualizing_iff
import Theorems.Thm_ConsistentSubmodular_Shadow_chain_fixedValue_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Shadow

/-- Summation by parts for the mean left endpoint: `Σ_{j ≤ n} p_j ℓ_j = ℓ_n / d_n - n`. -/
theorem sum_chainProb_mul_left {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i ≤ n, d i ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), chainProb d j * chainLeft d j = chainLeft d n / d n - n := by
  induction n with
  | zero => simp [chainProb, chainLeft]
  | succ n ih =>
    have hL : chainLeft d (n + 1) = chainLeft d n + d n := Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, ih fun i hi => hd i (by omega), chainProb, hL]
    have h1 := hd n (by omega)
    have h2 := hd (n + 1) le_rfl
    field_simp
    push_cast
    ring

/-- Summation by parts for the mean length: `Σ_{j ≤ n} p_j d_j = 1 + Σ_{j<n} (1 - d_{j+1}/d_j)`. -/
theorem sum_chainProb_mul_length {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i ≤ n, d i ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), chainProb d j * d j =
      1 + ∑ j ∈ Finset.range n, (1 - d (j + 1) / d j) := by
  induction n with
  | zero => simp [chainProb, hd 0 le_rfl]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih fun i hi => hd i (by omega), Finset.sum_range_succ, chainProb]
    have h1 := hd n (by omega)
    have h2 := hd (n + 1) le_rfl
    field_simp
    ring

theorem sum_Iic_val {N : ℕ} (f : ℕ → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i ∈ Finset.range (j + 1), f i := by
  have h := Finset.sum_map (Finset.Iic j) Fin.valEmbedding f
  rw [Fin.map_valEmbedding_Iic] at h
  have hI : (Finset.Iic (j : ℕ)) = Finset.range (j + 1) := by
    ext x
    simp
  rw [hI] at h
  simpa using h.symm

section

variable {N : ℕ} {d : ℕ → ℝ}

variable (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1)

theorem chainInstance_consecutive : (chainInstance N d hd hN).IsNonincreasingConsecutive := by
  refine ⟨by simp [chainInstance, chainLeft], fun i => ?_, fun i => ?_, ?_⟩
  · simp [chainInstance, chainLeft, Finset.sum_range_succ]
  · simp only [chainInstance, Fin.val_succ, Fin.val_castSucc, add_sub_cancel_left]
    exact hd i i.isLt
  · simp [chainInstance, hN]

/-- The probabilities `chainProb` have the cumulative sums (5), so they are the equalizing
distribution of the chain. -/
theorem chainInstance_equalizing : (chainInstance N d hd hN).IsEqualizing := by
  rw [Chains.isEqualizing_iff (chainInstance_consecutive hd hN)]
  intro j
  simp only [Chains.intervalLength, chainInstance, Fin.val_last, add_sub_cancel_left, hN]
  rw [sum_Iic_val (chainProb d) j, sum_chainProb]

/-- At realization `j` the interval `j` itself is available, so the expected value in hindsight
is at least `Σ_j p_j (ℓ_j + d_j)`. -/
theorem chain_adaptiveValue_ge :
    ∑ j : Fin (N + 1), chainProb d j * (chainLeft d j + d j) ≤
      (chainInstance N d hd hN).adaptiveValue := by
  refine Finset.sum_le_sum fun j _ => ?_
  have hj := j.isLt
  refine mul_le_mul_of_nonneg_left ?_ (chainProb_nonneg hd hN (by omega))
  refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun i => (chainInstance N d hd hN).value i j)
    (Finset.mem_univ j))
  simp only [chainInstance, IntervalInstance.value, max_self, add_sub_cancel_left]
  rw [max_eq_right (chain_pos hd hN (show (j : ℕ) ≤ N by omega)).le]

end

end ConsistentSubmodular.Shadow

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Shadow

theorem solution {α : ℝ} (hα : 0 ≤ α) (hchain : ChainHypothesis α) {N : ℕ} {d : ℕ → ℝ}
    (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) :
    α * ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j) ≤
      (1 - α) * (1 + ∑ j ∈ Finset.range N, (d j - 1)) := by
  have hne : ∀ i ≤ N, d i ≠ 0 := fun i hi => (chain_pos hd hN hi).ne'
  -- `B = Σ_j p_j ℓ_j = Σ_{j<N} (d_j - 1)` and `C = Σ_j p_j d_j = 1 + Σ_{j<N} (1 - d_{j+1}/d_j)`.
  have hB : ∑ j : Fin (N + 1), chainProb d j * chainLeft d j =
      ∑ j ∈ Finset.range N, (d j - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => chainProb d j * chainLeft d j) (N + 1),
      sum_chainProb_mul_left hne, hN, div_one, chainLeft, Finset.sum_sub_distrib]
    simp
  have hC : ∑ j : Fin (N + 1), chainProb d j * d j =
      1 + ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => chainProb d j * d j) (N + 1),
      sum_chainProb_mul_length hne]
  have hfix := chain_fixedValue_le hd hN
  have hada := chain_adaptiveValue_ge hd hN
  simp only [mul_add, Finset.sum_add_distrib] at hada
  rw [hB] at hfix hada
  rw [hC] at hada
  set B := ∑ j ∈ Finset.range N, (d j - 1)
  set S := ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j hj =>
    sub_nonneg.mpr (chain_one_le hd hN (by have := Finset.mem_range.mp hj; omega))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j hj => by
    have hj := Finset.mem_range.mp hj
    rw [sub_nonneg, div_le_one (chain_pos hd hN (by omega))]
    exact hd j hj
  have hpos : 0 < (chainInstance N d hd hN).adaptiveValue := by linarith
  have hgap := hchain N _ (chainInstance_consecutive hd hN) (chainInstance_equalizing hd hN)
  rw [IntervalInstance.adaptivityGap, if_neg hpos.ne', le_div_iff₀ hpos] at hgap
  nlinarith [mul_le_mul_of_nonneg_left hada hα]

end
