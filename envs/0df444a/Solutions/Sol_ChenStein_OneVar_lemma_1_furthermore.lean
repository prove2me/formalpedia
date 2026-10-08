-- Prove2me | solution 1 for ChenStein.OneVar.lemma_1_furthermore
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:13:58.600981+00:00
-- url     : https://prove2.me/submissions/ec6894e5-80a3-494d-a908-d02fa39e4835

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting



namespace ChenStein.OneVar

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

lemma hasSum_exp_series (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

lemma exp_tail_bounds (x : ℝ) (hx : 0 ≤ x) (w : ℕ) :
    0 ≤ Real.exp x - ∑ k ∈ Finset.range (w + 1), x ^ k / (k.factorial : ℝ) ∧
    Real.exp x - ∑ k ∈ Finset.range (w + 1), x ^ k / (k.factorial : ℝ) ≤
      x ^ w / (w.factorial : ℝ) * (Real.exp x - 1) := by
  set f : ℕ → ℝ := fun n => x ^ n / (n.factorial : ℝ) with hf
  have hs : Summable f := (hasSum_exp_series x).summable
  have hsum : ∑' n, f n = Real.exp x := (hasSum_exp_series x).tsum_eq
  have h1 : Real.exp x - ∑ k ∈ Finset.range (w + 1), f k = ∑' i, f (i + (w + 1)) := by
    rw [← hsum, ← Summable.sum_add_tsum_nat_add (w + 1) hs]; ring
  have h2 : Real.exp x - 1 = ∑' i, f (i + 1) := by
    rw [← hsum, ← Summable.sum_add_tsum_nat_add 1 hs]
    simp [hf]
  have hnn : ∀ n, 0 ≤ f n := fun n => by simp only [hf]; positivity
  refine ⟨?_, ?_⟩
  · rw [h1]; exact tsum_nonneg (fun i => hnn _)
  · rw [h1, h2, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) ((summable_nat_add_iff (w + 1)).mpr hs)
      (((summable_nat_add_iff 1).mpr hs).mul_left _)
    simp only [hf]
    have hfac : ((w.factorial : ℝ) * ((i + 1).factorial : ℝ)) ≤ ((i + (w + 1)).factorial : ℝ) := by
      have := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add w (i + 1))
      rw [show i + (w + 1) = w + (i + 1) by ring]
      exact_mod_cast this
    have hpow : x ^ (i + (w + 1)) = x ^ w * x ^ (i + 1) := by rw [show i + (w + 1) = w + (i + 1) by ring, pow_add]
    rw [hpow, show x ^ w / (w.factorial : ℝ) * (x ^ (i + 1) / ((i + 1).factorial : ℝ))
        = x ^ w * x ^ (i + 1) / ((w.factorial : ℝ) * ((i + 1).factorial : ℝ)) by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hfac

lemma S_zero' (lam : ℝ≥0) (h : ℕ → ℝ) : S lam h 0 = 0 := by
  simp [S]

lemma S_succ' (lam : ℝ≥0) (h : ℕ → ℝ) (n : ℕ) :
    S lam h (n + 1) = -((lam : ℝ)⁻¹) * (poissonPMFReal lam n)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), h k * poissonPMFReal lam k := by
  simp [S]

lemma sum_h_pmf (lam : ℝ≥0) (w : ℕ) :
    ∑ k ∈ Finset.range (w + 1), ((if k = 0 then (1 : ℝ) else 0) - Real.exp (-(lam : ℝ))) *
      poissonPMFReal lam k
    = Real.exp (-(lam : ℝ)) * (1 - Real.exp (-(lam : ℝ)) *
        ∑ k ∈ Finset.range (w + 1), (lam : ℝ) ^ k / (k.factorial : ℝ)) := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' (Finset.range (w + 1)) 0]
  simp only [Finset.mem_range, Nat.zero_lt_succ, if_true]
  unfold poissonPMFReal
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem lemma_1_furthermore_core (lam : ℝ≥0) (hlam : 0 < lam) :
    (∀ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| ≤
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) ∧
    (∃ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| =
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) := by
  have hl : (0 : ℝ) < lam := hlam
  set E := Real.exp (lam : ℝ) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (le_of_lt hl)
  have hneg : Real.exp (-(lam : ℝ)) = E⁻¹ := by rw [Real.exp_neg]
  have hpos : ∀ n, 0 < poissonPMFReal lam n := fun n => poissonPMFReal_pos hlam
  -- closed form of S at w + 1
  have hS : ∀ w, S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) (w + 1)
      = -((w.factorial : ℝ) * (E - ∑ k ∈ Finset.range (w + 1), (lam : ℝ) ^ k / (k.factorial : ℝ)))
          / ((lam : ℝ) * (lam : ℝ) ^ w * E) := by
    intro w
    rw [S_succ', sum_h_pmf, hneg]
    unfold poissonPMFReal
    rw [hneg]
    have hw : (0 : ℝ) < (w.factorial : ℝ) := by positivity
    field_simp
    try ring
  have hbound : ∀ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) (w + 1)|
      ≤ (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ) := by
    intro w
    obtain ⟨ht0, ht1⟩ := exp_tail_bounds (lam : ℝ) (le_of_lt hl) w
    rw [hS, neg_div, abs_neg, abs_of_nonneg (by positivity), hneg]
    have hw : (0 : ℝ) < (w.factorial : ℝ) := by positivity
    have hlw : (0 : ℝ) < (lam : ℝ) ^ w := by positivity
    rw [div_le_div_iff₀ (by positivity) hl]
    have key : (w.factorial : ℝ) * (E - ∑ k ∈ Finset.range (w + 1), (lam : ℝ) ^ k / (k.factorial : ℝ))
        ≤ (lam : ℝ) ^ w * (E - 1) := by
      have := ht1
      rw [div_mul_eq_mul_div, le_div_iff₀ hw] at this
      linarith
    have hEinv : (1 - E⁻¹) * E = E - 1 := by field_simp
    calc (w.factorial : ℝ) * (E - ∑ k ∈ Finset.range (w + 1), (lam : ℝ) ^ k / (k.factorial : ℝ)) * (lam : ℝ)
        ≤ (lam : ℝ) ^ w * (E - 1) * (lam : ℝ) := by
          exact mul_le_mul_of_nonneg_right key (le_of_lt hl)
      _ = (1 - E⁻¹) * ((lam : ℝ) * (lam : ℝ) ^ w * E) := by rw [← hEinv]; ring
  refine ⟨?_, ⟨1, ?_⟩⟩
  · intro w
    rcases w with _ | w
    · rw [S_zero', abs_zero, hneg]
      apply div_nonneg _ (le_of_lt hl)
      rw [sub_nonneg]
      exact inv_le_one_of_one_le₀ hE1
    · exact hbound w
  · rw [hS 0, neg_div, abs_neg, hneg]
    have h0 : ∑ x ∈ Finset.range (0 + 1), (lam : ℝ) ^ x / (x.factorial : ℝ) = 1 := by simp
    rw [h0]
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one]
    rw [abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
    field_simp

end ChenStein.OneVar

open ChenStein.OneVar
open scoped NNReal ENNReal

theorem solution (lam : ℝ≥0) (hlam : 0 < lam) :
    (∀ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| ≤
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) ∧
    (∃ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| =
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) := by
  exact lemma_1_furthermore_core lam hlam
