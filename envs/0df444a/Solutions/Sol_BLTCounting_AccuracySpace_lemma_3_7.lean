-- Prove2me | solution 1 for BLTCounting.AccuracySpace.lemma_3_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:20:24.103009+00:00
-- url     : https://prove2.me/submissions/10210434-02f6-48bc-8728-a0b6667554c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Theorems.Thm_BLTCounting_AccuracySpace_equation_19

open Complex Filter Topology BLTCounting.AccuracySpace

namespace AuxLemma37

lemma norm_sq_add_nat (x : ℝ) (j : ℕ) :
    ‖(1 / 4 : ℂ) + I * (x : ℂ) + (j : ℂ)‖ ^ 2 = (1 / 4 + (j : ℝ)) ^ 2 + x ^ 2 := by
  have hz : (1 / 4 : ℂ) + I * (x : ℂ) + (j : ℂ) = ((1 / 4 + (j : ℝ) : ℝ) : ℂ) + (x : ℂ) * I := by
    push_cast
    ring
  rw [hz, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]

lemma gamma_norm_sq_strictAnti {x₁ x₂ : ℝ} (hx₁ : 0 ≤ x₁) (hlt : x₁ < x₂) :
    ‖Complex.Gamma (1 / 4 + I * (x₂ : ℂ))‖ ^ 2 <
      ‖Complex.Gamma (1 / 4 + I * (x₁ : ℂ))‖ ^ 2 := by
  let z₁ : ℂ := 1 / 4 + I * (x₁ : ℂ)
  let z₂ : ℂ := 1 / 4 + I * (x₂ : ℂ)
  have hx₂_pos : 0 < x₂ := lt_of_le_of_lt hx₁ hlt
  have hx_sq : x₁ ^ 2 < x₂ ^ 2 :=
    sq_lt_sq.mpr (by rw [abs_of_nonneg hx₁, abs_of_pos hx₂_pos]; exact hlt)
  have hz₁_0_pos : 0 < ‖z₁ + ((0 : ℕ) : ℂ)‖ ^ 2 := by
    rw [norm_sq_add_nat x₁ 0]
    positivity
  have hz₂_0_pos : 0 < ‖z₂ + ((0 : ℕ) : ℂ)‖ ^ 2 := by
    rw [norm_sq_add_nat x₂ 0]
    positivity
  let q : ℝ := ‖z₁ + ((0 : ℕ) : ℂ)‖ ^ 2 / ‖z₂ + ((0 : ℕ) : ℂ)‖ ^ 2
  have hq_pos : 0 < q := div_pos hz₁_0_pos hz₂_0_pos
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [div_lt_one hz₂_0_pos, norm_sq_add_nat x₁ 0, norm_sq_add_nat x₂ 0]
    linarith
  have hseq_le : ∀ᶠ n : ℕ in atTop, ‖z₂.GammaSeq n‖ ^ 2 ≤ q * ‖z₁.GammaSeq n‖ ^ 2 := by
    refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    unfold Complex.GammaSeq
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hcpow₁ : ‖((n : ℂ)) ^ z₁‖ = (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hre : z₁.re = 1 / 4 := by simp [z₁]
      simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hn_pos z₁
    have hcpow₂ : ‖((n : ℂ)) ^ z₂‖ = (n : ℝ) ^ (1 / 4 : ℝ) := by
      have hre : z₂.re = 1 / 4 := by simp [z₂]
      simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hn_pos z₂
    simp only [norm_div, norm_mul, norm_prod, div_pow, mul_pow, ← Finset.prod_pow]
    rw [hcpow₁, hcpow₂]
    let num : ℝ := ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * ‖((Nat.factorial n : ℂ))‖ ^ 2
    let p₁ : ℝ := ∏ j ∈ Finset.range (n + 1), ‖z₁ + (j : ℂ)‖ ^ 2
    let p₂ : ℝ := ∏ j ∈ Finset.range (n + 1), ‖z₂ + (j : ℂ)‖ ^ 2
    change num / p₂ ≤ q * (num / p₁)
    have hnum_nn : 0 ≤ num := by positivity
    have hp₁_pos : 0 < p₁ := by
      refine Finset.prod_pos fun j _ => ?_
      rw [norm_sq_add_nat x₁ j]
      positivity
    have hp₂_pos : 0 < p₂ := by
      refine Finset.prod_pos fun j _ => ?_
      rw [norm_sq_add_nat x₂ j]
      positivity
    have hp_rel : p₁ ≤ q * p₂ := by
      have hsplit₁ : p₁ = (∏ j ∈ Finset.range n, ‖z₁ + ((j + 1 : ℕ) : ℂ)‖ ^ 2) *
          ‖z₁ + ((0 : ℕ) : ℂ)‖ ^ 2 := Finset.prod_range_succ' _ n
      have hsplit₂ : p₂ = (∏ j ∈ Finset.range n, ‖z₂ + ((j + 1 : ℕ) : ℂ)‖ ^ 2) *
          ‖z₂ + ((0 : ℕ) : ℂ)‖ ^ 2 := Finset.prod_range_succ' _ n
      have htail : (∏ j ∈ Finset.range n, ‖z₁ + ((j + 1 : ℕ) : ℂ)‖ ^ 2) ≤
          ∏ j ∈ Finset.range n, ‖z₂ + ((j + 1 : ℕ) : ℂ)‖ ^ 2 := by
        refine Finset.prod_le_prod (fun j _ => sq_nonneg _) fun j _ => ?_
        rw [norm_sq_add_nat x₁ (j + 1), norm_sq_add_nat x₂ (j + 1)]
        linarith
      calc
        p₁ = (∏ j ∈ Finset.range n, ‖z₁ + ((j + 1 : ℕ) : ℂ)‖ ^ 2) *
            ‖z₁ + ((0 : ℕ) : ℂ)‖ ^ 2 := hsplit₁
        _ ≤ (∏ j ∈ Finset.range n, ‖z₂ + ((j + 1 : ℕ) : ℂ)‖ ^ 2) *
            ‖z₁ + ((0 : ℕ) : ℂ)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right htail hz₁_0_pos.le
        _ = q * ((∏ j ∈ Finset.range n, ‖z₂ + ((j + 1 : ℕ) : ℂ)‖ ^ 2) *
            ‖z₂ + ((0 : ℕ) : ℂ)‖ ^ 2) := by
          dsimp [q]
          rw [mul_comm (‖z₁ + ((0 : ℕ) : ℂ)‖ ^ 2 / ‖z₂ + ((0 : ℕ) : ℂ)‖ ^ 2), mul_assoc]
          congr 1
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hz₂_0_pos)]
        _ = q * p₂ := by rw [← hsplit₂]
    rw [div_le_iff₀ hp₂_pos]
    calc
      num = (num / p₁) * p₁ := by rw [div_mul_cancel₀ _ (ne_of_gt hp₁_pos)]
      _ ≤ (num / p₁) * (q * p₂) :=
        mul_le_mul_of_nonneg_left hp_rel (div_nonneg hnum_nn hp₁_pos.le)
      _ = q * (num / p₁) * p₂ := by ring
  have ht₁ : Tendsto (fun n => ‖z₁.GammaSeq n‖ ^ 2) atTop (𝓝 (‖Complex.Gamma z₁‖ ^ 2)) :=
    ((Complex.GammaSeq_tendsto_Gamma z₁).norm).pow 2
  have ht₂ : Tendsto (fun n => ‖z₂.GammaSeq n‖ ^ 2) atTop (𝓝 (‖Complex.Gamma z₂‖ ^ 2)) :=
    ((Complex.GammaSeq_tendsto_Gamma z₂).norm).pow 2
  have hlim_le : ‖Complex.Gamma z₂‖ ^ 2 ≤ q * ‖Complex.Gamma z₁‖ ^ 2 :=
    le_of_tendsto_of_tendsto ht₂ (ht₁.const_mul q) hseq_le
  have hgamma₁_pos : 0 < ‖Complex.Gamma z₁‖ ^ 2 := by
    have hne : Complex.Gamma z₁ ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp [z₁])
    positivity
  nlinarith

end AuxLemma37

theorem solution :
    (∀ x : ℝ, (c0Hat x).im = 0 ∧ 0 ≤ (c0Hat x).re ∧ c0Hat (-x) = c0Hat x) ∧
      StrictAntiOn (fun x : ℝ => (c0Hat x).re) (Set.Ici 0) := by
  refine ⟨fun x => ?_, fun x₁ hx₁ x₂ _ hlt => ?_⟩
  · have hx := equation_19 x
    have hnx := equation_19 (-x)
    refine ⟨?_, ?_, ?_⟩
    · rw [hx]
      exact Complex.ofReal_im _
    · rw [hx]
      simp only [Complex.ofReal_re]
      exact div_nonneg (sq_nonneg _) Real.pi_pos.le
    · rw [hnx, hx]
      have hconj : (1 / 4 : ℂ) + I * ((-x : ℝ) : ℂ) =
          (starRingEnd ℂ) ((1 / 4 : ℂ) + I * (x : ℂ)) := by
        simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I,
          Complex.conj_ofReal]
        push_cast
        ring
      rw [hconj, Complex.Gamma_conj, RCLike.norm_conj]
  · dsimp only
    rw [equation_19 x₁, equation_19 x₂]
    simp only [Complex.ofReal_re]
    exact div_lt_div_of_pos_right (AuxLemma37.gamma_norm_sq_strictAnti hx₁ hlt) Real.pi_pos
