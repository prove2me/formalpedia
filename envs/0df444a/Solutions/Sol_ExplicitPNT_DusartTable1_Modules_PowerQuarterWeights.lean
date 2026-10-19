-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:30:37.214129+00:00
-- url     : https://prove2.me/submissions/398c01e2-5bb1-43de-8f0d-4168e50ca0e5

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterAbel

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_positive_inverse_le_quarter : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, ρ.im ≤ T),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im)) ≤
      40 * T^(1 / 4 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel.2.2.1

private theorem finite_positive_inverse_cube_tail_quarter : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 4 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (96 / 7 : ℝ) * T^(-7 / 4 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel.2.2.2

private theorem finite_absolute_weight_le (W : ℝ → ℝ) (B : ℝ)
    (hpos : ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) →
      (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ B)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|) ≤ 2 * B := by
  classical
  let Zp := Z.filter (fun ρ => 0 < ρ.im)
  let Zn := Z.filter (fun ρ => ¬0 < ρ.im)
  have hpositive : ∀ ρ ∈ Zp, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨hmem, hγ⟩ := Finset.mem_filter.mp hρ
    exact ⟨hZ ρ hmem, hγ⟩
  have hnegative : ∀ ρ ∈ Zn, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ ρ.im < 0 := by
    intro ρ hρ
    obtain ⟨hmem, hγ⟩ := Finset.mem_filter.mp hρ
    have hnt := hZ ρ hmem
    have hn : ρ.im ≠ 0 := by
      intro he
      have hh := DusartSmoothing.RvM.nontrivial_zero_abs_height ρ hnt
      rw [he, abs_zero] at hh
      linarith [Real.pi_pos]
    exact ⟨hnt, lt_of_le_of_ne (le_of_not_gt hγ) hn⟩
  let C := Zn.image (starRingEnd ℂ)
  have hC : ∀ ρ ∈ C, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨hnt, him⟩ := hnegative τ hτ
    refine ⟨⟨?_, by simpa using hnt.2.1, by simpa using hnt.2.2⟩, ?_⟩
    · rw [riemannZeta_conj, hnt.1, map_zero]
    · simpa using neg_pos.mpr him
  have hB := hpos C hC
  dsimp [C] at hB
  rw [Finset.sum_image (fun a _ b _ he => by
    have hh := congrArg (starRingEnd ℂ) he
    simpa using hh)] at hB
  have he : (∑ ρ ∈ Zn, (DusartSmoothing.RvM.zeroMult (starRingEnd ℂ ρ) : ℝ) *
      W (starRingEnd ℂ ρ).im) =
      ∑ ρ ∈ Zn, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im| := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hnt := (hnegative ρ hρ).1
    have hne : ρ ≠ 1 := by
      intro h
      have hσ := hnt.2.2
      rw [h] at hσ
      norm_num at hσ
    rw [DusartSmoothing.RvM.zeroMult_conj ρ hne]
    simp only [Complex.conj_im, abs_of_neg (hnegative ρ hρ).2]
  rw [he] at hB
  have hP : (∑ ρ ∈ Zp, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|) ≤ B := by
    calc
      _ = ∑ ρ ∈ Zp, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W ρ.im := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [abs_of_pos (hpositive ρ hρ).2]
      _ ≤ B := hpos Zp hpositive
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 < ρ.im)
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|)
  change (∑ ρ ∈ Zp, _) + (∑ ρ ∈ Zn, _) = _ at hsplit
  linarith

private theorem finite_positive_split_kernel_bound (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / ρ.im) (4 * T^2 / ρ.im^3)) ≤ (664 / 7 : ℝ) * T^(1 / 4 : ℝ) := by
  classical
  let L := Z.filter (fun ρ => ρ.im ≤ T)
  let H := Z.filter (fun ρ => ¬ρ.im ≤ T)
  have hL : ∀ ρ ∈ L, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    exact hZ ρ (Finset.mem_filter.mp hρ).1
  have hH : ∀ ρ ∈ H, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
    intro ρ hρ
    exact hZ ρ (Finset.mem_filter.mp hρ).1
  have hlow := finite_positive_inverse_le_quarter L hL T hT
    (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hhigh := finite_positive_inverse_cube_tail_quarter H hH T hT
    (fun ρ hρ => (lt_of_not_ge (Finset.mem_filter.mp hρ).2).le)
  have h1 : (∑ ρ ∈ L, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / ρ.im) (4 * T^2 / ρ.im^3)) ≤ 40 * T^(1 / 4 : ℝ) := by
    apply le_trans (Finset.sum_le_sum (fun ρ _ =>
      mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _))) hlow
  have h2 : (∑ ρ ∈ H, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / ρ.im) (4 * T^2 / ρ.im^3)) ≤
      4 * T^2 * ((96 / 7 : ℝ) * T^(-7 / 4 : ℝ)) := by
    calc
      _ ≤ ∑ ρ ∈ H, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (4 * T^2 / ρ.im^3) :=
        Finset.sum_le_sum (fun ρ _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg _))
      _ = 4 * T^2 * (∑ ρ ∈ H, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ρ _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhigh (by positivity)
  have hpow : T^2 * T^(-7 / 4 : ℝ) = T^(1 / 4 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_add (by linarith : 0 < T)]
    norm_num
  have he : 4 * T^2 * ((96 / 7 : ℝ) * T^(-7 / 4 : ℝ)) =
      (384 / 7 : ℝ) * T^(1 / 4 : ℝ) := by
    calc
      _ = (384 / 7 : ℝ) * (T^2 * T^(-7 / 4 : ℝ)) := by ring
      _ = _ := by rw [hpow]
  rw [he] at h2
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ => ρ.im ≤ T)
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ) * min (1 / ρ.im) (4 * T^2 / ρ.im^3))
  change (∑ ρ ∈ L, _) + (∑ ρ ∈ H, _) = _ at hsplit
  linarith

private theorem finite_absolute_split_kernel_bound (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / |ρ.im|) (4 * T^2 / |ρ.im|^3)) ≤ (1328 / 7 : ℝ) * T^(1 / 4 : ℝ) := by
  have hh := finite_absolute_weight_le
    (fun t => min (1 / t) (4 * T^2 / t^3)) ((664 / 7 : ℝ) * T^(1 / 4 : ℝ))
    (finite_positive_split_kernel_bound T hT) Z hZ
  linarith

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (W : ℝ → ℝ) (B : ℝ)
    (hpos : ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) →
      (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ B)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|) ≤ 2 * B
) ∧
(
    ∀ (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / ρ.im) (4 * T^2 / ρ.im^3)) ≤ (664 / 7 : ℝ) * T^(1 / 4 : ℝ)
) ∧
(
    ∀ (T : ℝ) (hT : 4 ≤ T) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) *
      min (1 / |ρ.im|) (4 * T^2 / |ρ.im|^3)) ≤ (1328 / 7 : ℝ) * T^(1 / 4 : ℝ)
) := by
  exact ⟨finite_absolute_weight_le, finite_positive_split_kernel_bound, finite_absolute_split_kernel_bound⟩
