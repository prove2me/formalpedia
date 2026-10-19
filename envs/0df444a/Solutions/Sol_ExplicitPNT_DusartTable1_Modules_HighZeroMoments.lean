-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.HighZeroMoments
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:40:19.630978+00:00
-- url     : https://prove2.me/submissions/8a091344-1f5a-4856-b35c-9adc1014dcba

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_SharpNumericalZeroTail
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_AbsoluteNumericalZeroTail

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_positive_inverse_cube_tail_H_sharp : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      (4 / 10^25 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.SharpNumericalZeroTail.2.2.2.2

private theorem finite_absolute_inverse_cube_tail_H : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤
      (8 / 10^25 : ℝ) :=
  ExplicitPNT.DusartTable1.Modules.AbsoluteNumericalZeroTail.1

private theorem finite_weighted_inverse_power_from_cube {ι : Type*} (S : Finset ι)
    (γ w : ι → ℝ) (H B : ℝ) (hH : 0 < H)
    (hγ : ∀ ρ ∈ S, H ≤ γ ρ) (hw : ∀ ρ ∈ S, 0 ≤ w ρ)
    (hcube : (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^3)) ≤ B) (n : ℕ) :
    (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^(n + 3))) ≤ B / H^n := by
  have hterm (ρ : ι) (hρ : ρ ∈ S) :
      w ρ * (1 / (γ ρ)^(n + 3)) ≤ (1 / H^n) * (w ρ * (1 / (γ ρ)^3)) := by
    have hp := pow_le_pow_left₀ hH.le (hγ ρ hρ) n
    have hγ0 : 0 < γ ρ := hH.trans_le (hγ ρ hρ)
    have hh : 1 / (γ ρ)^(n + 3) ≤ (1 / H^n) * (1 / (γ ρ)^3) := by
      rw [pow_add]
      calc
        _ ≤ 1 / (H^n * (γ ρ)^3) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hp (by positivity))
        _ = _ := by ring
    have hm := mul_le_mul_of_nonneg_left hh (hw ρ hρ)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  calc
    _ ≤ ∑ ρ ∈ S, (1 / H^n) * (w ρ * (1 / (γ ρ)^3)) :=
      Finset.sum_le_sum (fun ρ hρ => hterm ρ hρ)
    _ = (1 / H^n) * (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^3)) := by rw [Finset.mul_sum]
    _ ≤ (1 / H^n) * B := mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring

private theorem finite_positive_high_zero_moments (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im) (n : ℕ) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^(n + 3))) ≤
      (4 / 10^25 : ℝ) / (2445999556030 : ℝ)^n := by
  exact finite_weighted_inverse_power_from_cube Z Complex.im
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ)) 2445999556030 (4 / 10^25)
    (by norm_num) (fun ρ hρ => (hγ ρ hρ).le) (fun _ _ => Nat.cast_nonneg _)
    (finite_positive_inverse_cube_tail_H_sharp Z hZ hγ) n

private theorem finite_absolute_high_zero_moments (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|) (n : ℕ) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n := by
  exact finite_weighted_inverse_power_from_cube Z (fun ρ => |ρ.im|)
    (fun ρ => (DusartSmoothing.RvM.zeroMult ρ : ℝ)) 2445999556030 (8 / 10^25)
    (by norm_num) (fun ρ hρ => (hγ ρ hρ).le) (fun _ _ => Nat.cast_nonneg _)
    (finite_absolute_inverse_cube_tail_H Z hZ hγ) n

private theorem absolute_high_zero_moments (n : ℕ) :
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n := by
  classical
  apply Real.tsum_le_of_sum_le
  · intro ρ
    positivity
  · intro S
    let Z : Finset ℂ := S.image (fun ρ : StrictHighAbsoluteZero (2445999556030 : ℝ) => ρ.val)
    have hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.1
    have hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im| := by
      intro ρ hρ
      obtain ⟨τ, _, rfl⟩ := Finset.mem_image.mp hρ
      exact τ.property.2
    have hh := finite_absolute_high_zero_moments Z hZ hγ n
    dsimp [Z] at hh
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hh
    exact hh

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ {ι : Type*} (S : Finset ι)
    (γ w : ι → ℝ) (H B : ℝ) (hH : 0 < H)
    (hγ : ∀ ρ ∈ S, H ≤ γ ρ) (hw : ∀ ρ ∈ S, 0 ≤ w ρ)
    (hcube : (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^3)) ≤ B) (n : ℕ),
    (∑ ρ ∈ S, w ρ * (1 / (γ ρ)^(n + 3))) ≤ B / H^n
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < ρ.im) (n : ℕ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^(n + 3))) ≤
      (4 / 10^25 : ℝ) / (2445999556030 : ℝ)^n
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|) (n : ℕ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n
) ∧
(
    ∀ (n : ℕ),
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^(n + 3))) ≤
      (8 / 10^25 : ℝ) / (2445999556030 : ℝ)^n
) := by
  exact ⟨finite_weighted_inverse_power_from_cube, finite_positive_high_zero_moments, finite_absolute_high_zero_moments, absolute_high_zero_moments⟩
