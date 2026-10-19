-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.AbsoluteNumericalZeroTail
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:38:36.790733+00:00
-- url     : https://prove2.me/submissions/765ec976-f5c9-40c6-8af1-9b7c1ebb780e

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_PowerQuarterWeights

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

private theorem finite_absolute_weight_le : ∀ (W : ℝ → ℝ) (B : ℝ)
    (hpos : ∀ Z : Finset ℂ,
      (∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) →
      (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ B)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|) ≤ 2 * B :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterWeights.1

private theorem finite_absolute_inverse_cube_tail_H (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤
      (8 / 10^25 : ℝ) := by
  classical
  let W : ℝ → ℝ := fun t => if (2445999556030 : ℝ) < t then 1 / t^3 else 0
  have hpos (S : Finset ℂ)
      (hS : ∀ ρ ∈ S, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im) :
      (∑ ρ ∈ S, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W ρ.im) ≤ (4 / 10^25 : ℝ) := by
    let F := S.filter (fun ρ => (2445999556030 : ℝ) < ρ.im)
    have hF : ∀ ρ ∈ F, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im := by
      intro ρ hρ
      exact hS ρ (Finset.mem_filter.mp hρ).1
    have hh := finite_positive_inverse_cube_tail_H_sharp F hF
      (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    simpa only [F, W, Finset.sum_filter, mul_ite, mul_zero] using hh
  have hh := finite_absolute_weight_le W (4 / 10^25) hpos Z hZ
  have he : (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * W |ρ.im|) =
      ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3) := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [W, if_pos (hγ ρ hρ)]
  rw [he] at hh
  linarith

private theorem absolute_inverse_cube_tail_H :
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) ≤
      (8 / 10^25 : ℝ) := by
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
    have hh := finite_absolute_inverse_cube_tail_H Z hZ hγ
    dsimp [Z] at hh
    rw [Finset.sum_image (fun a _ b _ he => Subtype.val_injective he)] at hh
    exact hh

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ)
    (hγ : ∀ ρ ∈ Z, (2445999556030 : ℝ) < |ρ.im|),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / |ρ.im|^3)) ≤
      (8 / 10^25 : ℝ)
) ∧
(
    (∑' ρ : StrictHighAbsoluteZero (2445999556030 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / |ρ.val.im|^3)) ≤
      (8 / 10^25 : ℝ)
) := by
  exact ⟨finite_absolute_inverse_cube_tail_H, absolute_inverse_cube_tail_H⟩
