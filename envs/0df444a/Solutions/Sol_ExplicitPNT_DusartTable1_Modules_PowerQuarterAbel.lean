-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:28:44.968149+00:00
-- url     : https://prove2.me/submissions/a7c26e50-7419-4963-a44a-e5c9f266f3d2

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterCount

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem positive_zero_height_fourteen : ∀ (ρ : ℂ)
    (hρ : DusartSmoothing.RvM.IsNontrivialZero ρ) (hi : 0 < ρ.im),
    14 < ρ.im :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterCount.1

private theorem finite_zero_count_quarter : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 4 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ 8 * t^(5 / 4 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterCount.2.2.2

private theorem finite_count_integrable (Z : Finset ℂ) (a b : ℝ) :
    IntervalIntegrable (finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im) volume a b := by
  change IntervalIntegrable (fun t => ∑ ρ ∈ Z,
    (DusartSmoothing.RvM.zeroMult ρ : ℝ) * primeStep ρ.im t) volume a b
  have hs := IntervalIntegrable.sum Z (fun ρ _ =>
    ((primeStep_mono ρ.im).intervalIntegrable (μ := volume) (a := a) (b := b)).const_mul
      (DusartSmoothing.RvM.zeroMult ρ : ℝ))
  convert hs using 1 <;> try rfl
  funext t
  simp only [Finset.sum_apply]

private theorem finite_quarter_abel (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a b k : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) (hk : 0 < k) (hpk : (5 / 4 : ℝ) - k ≠ 0)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * ρ.im^(-k)) ≤
      8 * b^((5 / 4 : ℝ) - k) +
      (8 * k / ((5 / 4 : ℝ) - k)) *
        (b^((5 / 4 : ℝ) - k) - a^((5 / 4 : ℝ) - k)) := by
  let g : ℝ → ℝ := fun t => t^(-k)
  let d : ℝ → ℝ := fun t => -k * t^(-k - 1)
  let F : ℝ → ℝ := fun t => (-8 * k / ((5 / 4 : ℝ) - k)) * t^((5 / 4 : ℝ) - k)
  have hcont : ContinuousOn d (Icc a b) := by
    intro t ht
    have hn : t ≠ 0 := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    dsimp [d]
    fun_prop (disch := aesop)
  have hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t := by
    intro t ht
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  have hF : ∀ t ∈ uIcc a b,
      HasDerivAt F ((8 * t^(5 / 4 : ℝ)) * d t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hdF := (Real.hasDerivAt_rpow_const (p := (5 / 4 : ℝ) - k)
      (Or.inl ht0.ne')).const_mul (-8 * k / ((5 / 4 : ℝ) - k))
    apply hdF.congr_deriv
    dsimp [d]
    rw [show 8 * t^(5 / 4 : ℝ) * (-k * t^(-k - 1)) =
      (-8 * k) * (t^(5 / 4 : ℝ) * t^(-k - 1)) by ring,
      ← Real.rpow_add ht0]
    rw [show (5 / 4 : ℝ) + (-k - 1) = (5 / 4 : ℝ) - k - 1 by ring]
    rw [← mul_assoc, div_mul_cancel₀ _ hpk]
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hi : IntervalIntegrable (fun t => finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t)
      volume a b := (finite_count_integrable Z a b).mul_continuousOn
        (by simpa [uIcc_of_le hab] using hcont)
  have himaj : IntervalIntegrable (fun t => (8 * t^(5 / 4 : ℝ)) * d t) volume a b := by
    apply (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 4)).const_mul 8).intervalIntegrable (μ := volume) a b).mul_continuousOn
    simpa [uIcc_of_le hab] using hcont
  have hile : (∫ t in a..b, (8 * t^(5 / 4 : ℝ)) * d t) ≤
      ∫ t in a..b, finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t := by
    apply intervalIntegral.integral_mono_on hab himaj hi
    intro t ht
    exact mul_le_mul_of_nonpos_right (finite_zero_count_quarter Z hZ t (ha.trans ht.1))
      (by dsimp [d]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (by linarith [ht.1]) _))
  have hival : (∫ t in a..b, (8 * t^(5 / 4 : ℝ)) * d t) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF himaj
  have hQb : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im b =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp [primeStep, (hγ ρ hρ).2]
  have hc := finite_zero_count_quarter Z hZ b (ha.trans hab)
  rw [hQb] at hc
  have hterm : g b * (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)) ≤
      8 * b^((5 / 4 : ℝ) - k) := by
    calc
      _ ≤ g b * (8 * b^(5 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hb0.le _)
      _ = _ := by
        dsimp [g]
        rw [show b^(-k) * (8 * b^(5 / 4 : ℝ)) =
          8 * (b^(5 / 4 : ℝ) * b^(-k)) by ring, ← Real.rpow_add hb0]
        simp only [sub_eq_add_neg]
  have he := finite_zero_summation_by_parts Z DusartSmoothing.RvM.zeroMult Complex.im
    a b hab hγ g d hcont hd
  change (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ _
  rw [he]
  rw [hival] at hile
  dsimp [F] at hile
  have hneg : -8 * k / ((5 / 4 : ℝ) - k) = -(8 * k / ((5 / 4 : ℝ) - k)) := by ring
  rw [hneg] at hile
  linarith

private theorem finite_positive_inverse_le_quarter (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      40 * T^(1 / 4 : ℝ) := by
  have he := finite_quarter_abel Z hZ 4 T 1 (by norm_num) hT (by norm_num) (by norm_num)
    (fun ρ hρ => ⟨by linarith [positive_zero_height_fourteen ρ (hZ ρ hρ).1 (hZ ρ hρ).2], hγ ρ hρ⟩)
  norm_num [Real.rpow_neg_one] at he
  simp only [one_div]
  have hh := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (1 / 4 : ℝ)
  linarith

private theorem finite_positive_inverse_cube_tail_quarter (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (96 / 7 : ℝ) * T^(-7 / 4 : ℝ) := by
  classical
  by_cases hn : Z.Nonempty
  · let b : ℝ := max T (Z.sup' hn Complex.im)
    have hb : T ≤ b := le_max_left _ _
    have hγb (ρ : ℂ) (hρ : ρ ∈ Z) : ρ.im ≤ b :=
      (Finset.le_sup' Complex.im hρ).trans (le_max_right _ _)
    have he := finite_quarter_abel Z hZ T b 3 hT hb (by norm_num) (by norm_num)
      (fun ρ hρ => ⟨hγ ρ hρ, hγb ρ hρ⟩)
    have hre : ∀ ρ ∈ Z, ρ.im^(-(3 : ℝ)) = 1 / ρ.im^3 := by
      intro ρ hρ
      rw [Real.rpow_neg (hZ ρ hρ).2.le]
      norm_num [one_div]
    have hsum : (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * ρ.im^(-(3 : ℝ))) =
        ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [hre ρ hρ]
    rw [hsum] at he
    norm_num at he
    have hh := Real.rpow_nonneg (by linarith : 0 ≤ b) (-7 / 4 : ℝ)
    simp only [one_div, neg_div] at hh ⊢
    linarith
  · have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty]
    positivity

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (Z : Finset ℂ) (a b : ℝ),
    IntervalIntegrable (finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im) volume a b
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a b k : ℝ) (ha : 4 ≤ a) (hab : a ≤ b) (hk : 0 < k) (hpk : (5 / 4 : ℝ) - k ≠ 0)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im ∧ ρ.im ≤ b),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * ρ.im^(-k)) ≤
      8 * b^((5 / 4 : ℝ) - k) +
      (8 * k / ((5 / 4 : ℝ) - k)) *
        (b^((5 / 4 : ℝ) - k) - a^((5 / 4 : ℝ) - k))
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      40 * T^(1 / 4 : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (96 / 7 : ℝ) * T^(-7 / 4 : ℝ)
) := by
  exact ⟨finite_count_integrable, finite_quarter_abel, finite_positive_inverse_le_quarter, finite_positive_inverse_cube_tail_quarter⟩
