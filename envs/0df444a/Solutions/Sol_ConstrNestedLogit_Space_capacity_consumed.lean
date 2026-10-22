-- Prove2me | solution 1 for ConstrNestedLogit.Space.capacity_consumed
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:38:29.837777+00:00
-- url     : https://prove2.me/submissions/e8607629-7e49-406e-8fac-a4b78dbb182a

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

set_option autoImplicit false
open ConstrNestedLogit.Space

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ k, 0 < I.v i k)
    (hw : ∀ k, 0 < w i k) (hwc : ∀ k, w i k ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Fin n)
    (hj : oneFractional x j) (hpositive : 0 < utility I i u j) :
    c i ≤ (∑ k ∈ rounded x, w i k) + w i j := by
  obtain ⟨⟨hbox, hcap⟩, hopt⟩ := hx
  obtain ⟨hj0, hj1, hrest⟩ := hj
  -- the weight of x
  have hdec : ∀ k, w i k * x k = (if k ∈ rounded x then w i k else 0) + (if k = j then w i j * x j else 0) := by
    intro k
    by_cases hk : k = j
    · subst hk
      have : k ∉ rounded x := by
        unfold rounded; simp; exact hj1.ne
      simp [this]
    · rw [if_neg hk, add_zero]
      rcases hrest k hk with h | h
      · have : k ∉ rounded x := by unfold rounded; simp [h]
        simp [this, h]
      · have : k ∈ rounded x := by unfold rounded; simp [h]
        simp [this, h]
  have hW : ∑ k, w i k * x k = (∑ k ∈ rounded x, w i k) + w i j * x j := by
    rw [Finset.sum_congr rfl fun k _ => hdec k, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.sum_ite_eq']
    simp
  by_contra hcon
  push Not at hcon
  have hwj := hw j
  have hslack : ∑ k, w i k * x k < c i := by
    rw [hW]
    nlinarith
  set s := c i - ∑ k, w i k * x k with hs
  have hspos : 0 < s := by rw [hs]; linarith
  set δ := min (1 - x j) (s / w i j) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (div_pos hspos hwj)
  have hδ1 : δ ≤ 1 - x j := min_le_left _ _
  have hδ2 : δ * w i j ≤ s := by
    have : δ ≤ s / w i j := min_le_right _ _
    rwa [le_div_iff₀ hwj] at this
  set y : Fin n → ℝ := fun k => x k + δ * (Pi.single j (1 : ℝ) : Fin n → ℝ) k with hy
  have hyfeas : knapsackLPFeasible (w i) (c i) y := by
    refine ⟨fun k => ?_, ?_⟩
    · have hk := hbox k
      by_cases hkj : k = j
      · subst hkj
        simp only [hy, Pi.single_eq_same]
        constructor <;> nlinarith [hbox k]
      · simp only [hy, Pi.single_eq_of_ne hkj, mul_zero, add_zero]
        exact hk
    · have : ∑ k, w i k * y k = ∑ k, w i k * x k + δ * w i j := by
        simp only [hy, mul_add, Finset.sum_add_distrib]
        congr 1
        simp [Pi.single_apply, mul_comm]
      rw [this]
      linarith
  have hle := hopt y hyfeas
  unfold knapsackLPObjective at hle
  have hobj : ∑ k, utility I i u k * y k = ∑ k, utility I i u k * x k + δ * utility I i u j := by
    simp only [hy, mul_add, Finset.sum_add_distrib]
    congr 1
    simp [Pi.single_apply, mul_comm]
  rw [hobj] at hle
  nlinarith
