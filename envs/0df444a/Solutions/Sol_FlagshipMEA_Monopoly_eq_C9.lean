-- Prove2me | solution 1 for FlagshipMEA.Monopoly.eq_C9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:14:34.280647+00:00
-- url     : https://prove2.me/submissions/cdf98ca1-6746-420f-84d1-270a6db07d0b

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

open FlagshipMEA.Monopoly in
theorem solution {n : ℕ} (D : Data n) (hS : D.Standing)
    (m : Fin n → ℝ) (hm : Feasible m) (hM : 0 < tme m) :
    D.revenue m =
      (∑ i, m i * D.A i (tme m)) / (∑ i, m i * D.B i (tme m)) := by
  set T := tme m with hT
  have hTs : ∑ i, m i = T := rfl
  set W : ℝ := ∑ j, Real.exp ((D.u j + D.θ) / D.lam) with hW
  set S2 : ℝ := ∑ j, Real.exp ((D.u j + D.θ) / D.lam) * D.markup j with hS2
  have hattr : ∀ j, D.attraction m j =
      m j * Real.exp (D.u j / D.lam) + Real.exp ((D.u j + D.θ) / D.lam) := by
    intro j
    unfold Data.attraction Data.base
    rw [add_div, Real.exp_add]
    ring
  have hsum : ∑ j, D.attraction m j = ∑ j, m j * Real.exp (D.u j / D.lam) + W := by
    simp_rw [hattr]
    rw [Finset.sum_add_distrib]
  have hmk : ∑ j, D.markup j * D.attraction m j =
      ∑ j, m j * Real.exp (D.u j / D.lam) * D.markup j + S2 := by
    simp_rw [hattr, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl; intro j _; ring
    · rw [hS2]; apply Finset.sum_congr rfl; intro j _; ring
  have hA : ∑ i, m i * D.A i T = ∑ j, m j * Real.exp (D.u j / D.lam) * D.markup j + S2 := by
    unfold Data.A
    rw [← hS2]
    have : ∀ i, m i * (Real.exp (D.u i / D.lam) * D.markup i + 1 / T * S2) =
        m i * Real.exp (D.u i / D.lam) * D.markup i + m i * (1 / T * S2) := by
      intro i; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hTs]
    congr 1
    field_simp
  have hB : ∑ i, m i * D.B i T = ∑ j, m j * Real.exp (D.u j / D.lam) + W + 1 := by
    unfold Data.B
    rw [← hW]
    have : ∀ i, m i * (Real.exp (D.u i / D.lam) + 1 / T * W + 1 / T) =
        m i * Real.exp (D.u i / D.lam) + m i * (1 / T * W + 1 / T) := by
      intro i; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hTs]
    have : T * (1 / T * W + 1 / T) = W + 1 := by field_simp
    rw [this]
    ring
  unfold Data.revenue logitShare
  have : ∑ j, D.markup j * (D.attraction m j / (∑ k, D.attraction m k + 1)) =
      (∑ j, D.markup j * D.attraction m j) / (∑ k, D.attraction m k + 1) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [this, hmk, hsum, hA, hB]
