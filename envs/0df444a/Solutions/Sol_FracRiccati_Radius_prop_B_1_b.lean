-- Prove2me | solution 1 for FracRiccati.Radius.prop_B_1_b
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:00:03.478286+00:00
-- url     : https://prove2.me/submissions/af2bd63a-4b19-47a7-acff-f2d24ee84baa

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace Aux_FRR_B1b
open FracRiccati.Radius

lemma coeff_rec (α : ℝ) (lam mu nu : ℂ) (j : ℕ) : coeff α lam mu nu (j + 2) =
    (lam * ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ)
      + mu * coeff α lam mu nu (j + 1)) *
      ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ) := by
  rw [coeff, Finset.sum_attach (Finset.Ico 1 (j + 1))
    (fun ℓ => coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ))]

lemma rec_real (α l mm n : ℝ) (j : ℕ)
    (h : ∀ i ≤ j + 1, (coeff α l mm n i).im = 0) :
    coeff α l mm n (j + 2) =
      (((l * ∑ ℓ ∈ Finset.Ico 1 (j + 1), (coeff α l mm n ℓ).re * (coeff α l mm n (j + 1 - ℓ)).re
        + mm * (coeff α l mm n (j + 1)).re) *
        (Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1)) : ℝ) : ℂ) := by
  have hz : ∀ i ≤ j + 1, coeff α l mm n i = ((coeff α l mm n i).re : ℂ) :=
    fun i hi => Complex.ext (by simp) (by simp [h i hi])
  rw [coeff_rec]
  have hs : ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α (l : ℂ) (mm : ℂ) (n : ℂ) ℓ *
      coeff α (l : ℂ) (mm : ℂ) (n : ℂ) (j + 1 - ℓ) =
      ((∑ ℓ ∈ Finset.Ico 1 (j + 1), (coeff α l mm n ℓ).re * (coeff α l mm n (j + 1 - ℓ)).re : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [Finset.mem_Ico] at hℓ
    rw [← hz ℓ (by omega), ← hz (j + 1 - ℓ) (by omega)]
  rw [hs]
  push_cast
  rw [← hz (j + 1) le_rfl]

lemma gfac_nonneg (α : ℝ) (hα : 0 < α) (j : ℕ) :
    0 ≤ Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) / Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) := by
  have h1 : 0 < α * ((j + 1 : ℕ) : ℝ) := by positivity
  exact div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le (Real.Gamma_pos_of_pos (by linarith)).le

lemma main (α : ℝ) (hα : 0 < α) (l m n : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (hn : 0 ≤ n) (k : ℕ) :
    (coeff α l m n k).im = 0 ∧ (coeff α l 0 n k).im = 0 ∧
      0 ≤ (coeff α l 0 n k).re ∧ (coeff α l 0 n k).re ≤ (coeff α l m n k).re := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [coeff]
    | 1, _ =>
      have hG : 0 < Real.Gamma (α + 1) := Real.Gamma_pos_of_pos (by linarith)
      simp only [coeff]
      refine ⟨?_, ?_, ?_, le_rfl⟩
      · rw [← Complex.ofReal_div]; simp
      · rw [← Complex.ofReal_div]; simp
      · rw [← Complex.ofReal_div, Complex.ofReal_re]; positivity
    | j + 2, ih =>
      have h1 : ∀ i ≤ j + 1, (coeff α l m n i).im = 0 := fun i hi => (ih i (by omega)).1
      have h0 : ∀ i ≤ j + 1, (coeff α l ((0:ℝ):ℂ) n i).im = 0 := by
        intro i hi; simpa using (ih i (by omega)).2.1
      have e1 := rec_real α l m n j h1
      have e0 := rec_real α l 0 n j h0
      simp only [Complex.ofReal_zero] at e0
      rw [e1, e0]
      simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
      have hg := gfac_nonneg α hα j
      have hy : ∀ i ≤ j + 1, 0 ≤ (coeff α l 0 n i).re ∧ (coeff α l 0 n i).re ≤ (coeff α l m n i).re :=
        fun i hi => (ih i (by omega)).2.2
      have hS0 : 0 ≤ ∑ ℓ ∈ Finset.Ico 1 (j + 1), (coeff α l 0 n ℓ).re * (coeff α l 0 n (j + 1 - ℓ)).re := by
        apply Finset.sum_nonneg
        intro ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        exact mul_nonneg (hy ℓ (by omega)).1 (hy (j + 1 - ℓ) (by omega)).1
      have hS : ∑ ℓ ∈ Finset.Ico 1 (j + 1), (coeff α l 0 n ℓ).re * (coeff α l 0 n (j + 1 - ℓ)).re ≤
          ∑ ℓ ∈ Finset.Ico 1 (j + 1), (coeff α l m n ℓ).re * (coeff α l m n (j + 1 - ℓ)).re := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        have a1 := hy ℓ (by omega)
        have a2 := hy (j + 1 - ℓ) (by omega)
        exact mul_le_mul a1.2 a2.2 a2.1 (a1.1.trans a1.2)
      have hx : 0 ≤ (coeff α l m n (j + 1)).re := (hy (j + 1) le_rfl).1.trans (hy (j + 1) le_rfl).2
      refine ⟨by simp; positivity, ?_⟩
      simp only [zero_mul, add_zero]
      apply mul_le_mul_of_nonneg_right _ hg
      nlinarith [mul_le_mul_of_nonneg_left hS hl, mul_nonneg hm hx]

end Aux_FRR_B1b

open FracRiccati.Radius Aux_FRR_B1b in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2)
    (l m n : ℝ) (hl : 0 ≤ l) (hm : 0 ≤ m) (hn : 0 ≤ n) :
    (∀ k : ℕ, 1 ≤ k →
      (coeff α l m n k).im = 0 ∧ (coeff α l 0 n k).im = 0 ∧
      (coeff α l 0 n k).re ≤ (coeff α l m n k).re ∧ 0 ≤ (coeff α l 0 n k).re) ∧
    radius α (coeff α l m n) ≤ radius α (coeff α l 0 n) := by
  refine ⟨fun k _ => ?_, ?_⟩
  · obtain ⟨a, b, c, d⟩ := main α hα0 l m n hl hm hn k
    exact ⟨a, b, d, c⟩
  · unfold radius
    refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards with k
    obtain ⟨a, b, c, d⟩ := main α hα0 l m n hl hm hn k
    have hle : ‖coeff α l 0 n k‖₊ ≤ ‖coeff α l m n k‖₊ := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      have e1 : coeff α l m n k = ((coeff α l m n k).re : ℂ) := Complex.ext (by simp) (by simp [a])
      have e0 : coeff α l 0 n k = ((coeff α l 0 n k).re : ℂ) := Complex.ext (by simp) (by simp [b])
      rw [e1, e0, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg c,
        Real.norm_of_nonneg (c.trans d)]
      exact d
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    apply ENNReal.inv_le_inv.mpr
    apply ENNReal.rpow_le_rpow (by exact_mod_cast hle)
    positivity
