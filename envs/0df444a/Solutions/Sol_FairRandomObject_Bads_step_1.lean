-- Prove2me | solution 1 for FairRandomObject.Bads.step_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:35:00.688496+00:00
-- url     : https://prove2.me/submissions/4eef2558-51d0-4781-ae01-bb60f7ace365

import Mathlib
import Definitions.Def_FairRandomObject_Bads_Setting
import Definitions.Def_FairRandomObject_Bads_BottomHeavy
set_option autoImplicit false
open FairRandomObject.Bads

theorem solution {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) :
    (∀ i, 0 ≤ psi n θ x i) ∧ 1 ≤ ∑ i, psi n θ x i ∧
      (θ ≠ 0 → (¬ ∃ c : ℝ, ∀ i, x i = c) → 1 < ∑ i, psi n θ x i) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hSpos : 0 < ∑ i, x i := Finset.sum_pos (fun i _ => hx i) Finset.univ_nonempty
  have hmean : mean x = (∑ i, x i) / n := rfl
  have hmpos : 0 < mean x := by rw [hmean]; positivity
  have hnm : (n : ℝ) * mean x = ∑ i, x i := by rw [hmean]; field_simp
  -- part 1
  have hpos : ∀ i, 0 ≤ psi n θ x i := by
    intro i
    have hxS : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => (hx j).le) (Finset.mem_univ i)
    have h1 : 1 / (n : ℝ) ≤ mean x / x i := by
      rw [le_div_iff₀ (hx i), hmean, div_mul_eq_mul_div, one_mul]
      exact div_le_div_of_nonneg_right hxS hn0.le
    unfold psi
    have h2 : θ / ((n : ℝ) - 1) * (1 / (n : ℝ) - 1) ≤ θ / ((n : ℝ) - 1) * (mean x / x i - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 : θ / ((n : ℝ) - 1) * (1 / (n : ℝ) - 1) = -(θ / n) := by
      field_simp
      ring
    have h4 : θ / (n : ℝ) ≤ 1 / n := div_le_div_of_nonneg_right hθ1 hn0.le
    linarith
  -- the sum
  have hterm : ∀ i, mean x / x i - 1 = (mean x - x i) ^ 2 / (x i * mean x) + (mean x - x i) / mean x := by
    intro i
    have := hx i
    field_simp
    ring
  have hsum0 : ∑ i, (mean x - x i) / mean x = 0 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hnm, sub_self, zero_div]
  have hT : ∑ i, (mean x / x i - 1) = ∑ i, (mean x - x i) ^ 2 / (x i * mean x) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, hsum0, add_zero]
  have hTnn : 0 ≤ ∑ i, (mean x / x i - 1) := by
    rw [hT]
    exact Finset.sum_nonneg (fun i _ => by have := hx i; positivity)
  have hpsisum : ∑ i, psi n θ x i = 1 + θ / ((n : ℝ) - 1) * ∑ i, (mean x / x i - 1) := by
    unfold psi
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨hpos, ?_, ?_⟩
  · rw [hpsisum]
    have : 0 ≤ θ / ((n : ℝ) - 1) * ∑ i, (mean x / x i - 1) := by positivity
    linarith
  · intro hθ hne
    have hθp : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθ)
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ mean x := by
      by_contra hcon
      push_neg at hcon
      exact hne ⟨mean x, hcon⟩
    have hTpos : 0 < ∑ i, (mean x / x i - 1) := by
      rw [hT]
      apply Finset.sum_pos' (fun i _ => by have := hx i; positivity)
      refine ⟨i, Finset.mem_univ i, ?_⟩
      have := hx i
      have : mean x - x i ≠ 0 := fun h => hi (by linarith)
      positivity
    rw [hpsisum]
    have : 0 < θ / ((n : ℝ) - 1) * ∑ i, (mean x / x i - 1) := by positivity
    linarith
