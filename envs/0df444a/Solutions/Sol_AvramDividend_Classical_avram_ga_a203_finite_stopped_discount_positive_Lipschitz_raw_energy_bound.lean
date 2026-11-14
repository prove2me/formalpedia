-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a203_finite_stopped_discount_positive_Lipschitz_raw_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:07:19.25445+00:00
-- url     : https://prove2.me/submissions/eca2dc89-e47e-43f4-8aad-d4b4ceabaded

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Signed monotone physical discount differences multiplied by globally
Lipschitz original source value changes have a positive finite sum dominated
by the stopped raw Gaussian first-energy sum. -/
theorem solution
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (a u v R : ℕ → ℝ)
    (q Δ L : ℝ) (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
    (hDisc : ∀ i ∈ S, -(q * Δ) ≤ a i ∧ a i ≤ 0)
    (hLip : ∀ i ∈ S, |u i - v i| ≤ L * |R i|) :
    max (∑ i ∈ S, if A i then a i * (u i - v i) else 0) 0 ≤
      q * Δ * L * (∑ i ∈ S, if A i then |R i| else 0) := by
  classical
  have hnonneg : 0 ≤ q * Δ * L := by
    exact mul_nonneg (mul_nonneg hq hΔ) hL
  have hsum :
      (∑ i ∈ S, if A i then a i * (u i - v i) else 0) ≤
      q * Δ * L * (∑ i ∈ S, if A i then |R i| else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    by_cases ha : A i
    · simp only [if_pos ha]
      have hd := hDisc i hi
      have hb := hLip i hi
      have habs : |a i| ≤ q * Δ := by
        rw [abs_of_nonpos hd.2]
        linarith
      have h0 : 0 ≤ |u i - v i| := abs_nonneg _
      calc
        a i * (u i - v i) ≤ |a i * (u i - v i)| :=
          le_abs_self _
        _ = |a i| * |u i - v i| := abs_mul _ _
        _ ≤ (q * Δ) * |u i - v i| :=
          mul_le_mul_of_nonneg_right habs h0
        _ ≤ (q * Δ) * (L * |R i|) :=
          mul_le_mul_of_nonneg_left hb (mul_nonneg hq hΔ)
        _ = q * Δ * L * |R i| := by ring
    · simp only [if_neg ha]
      simpa only [mul_zero] using (le_refl (0 : ℝ))
  have hright : 0 ≤ q * Δ * L *
      (∑ i ∈ S, if A i then |R i| else 0) := by
    apply mul_nonneg hnonneg
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  exact max_le hsum hright
