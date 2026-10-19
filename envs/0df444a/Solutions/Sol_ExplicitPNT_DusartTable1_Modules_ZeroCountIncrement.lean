-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.ZeroCountIncrement
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:29:03.996235+00:00
-- url     : https://prove2.me/submissions/7e36b541-d691-4004-82c9-208c203aed55

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

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_zero_count_increment (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im) :
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t +
      (DusartSmoothing.RvM.Ncount 0 H : ℝ) ≤ (DusartSmoothing.RvM.Ncount 0 t : ℝ) := by
  classical
  let fH := DusartSmoothing.RvM.finite_zero_window (b := H) (by norm_num : (0 : ℝ) < 4)
  let ft := DusartSmoothing.RvM.finite_zero_window (b := t) (by norm_num : (0 : ℝ) < 4)
  let A := fH.toFinset
  let B := Z.filter (fun ρ => ρ.im ≤ t)
  have hA (ρ : ℂ) (hρ : ρ ∈ A) :
      DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 4 < ρ.im ∧ ρ.im ≤ H := by
    dsimp [A] at hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact hρ
  have hB (ρ : ℂ) (hρ : ρ ∈ B) :
      DusartSmoothing.RvM.IsNontrivialZero ρ ∧ H < ρ.im ∧ ρ.im ≤ t := by
    obtain ⟨hz, ht⟩ := Finset.mem_filter.mp hρ
    exact ⟨(hZ ρ hz).1, hγ ρ hz, ht⟩
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro ρ ha hb
    exact (not_lt_of_ge (hA ρ ha).2.2) (hB ρ hb).2.1
  have hsub : A ∪ B ⊆ ft.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset]
    rcases Finset.mem_union.mp hρ with ha | hb
    · exact ⟨(hA ρ ha).1, (hA ρ ha).2.1, (hA ρ ha).2.2.trans hHt⟩
    · exact ⟨(hB ρ hb).1, hH.trans_lt (hB ρ hb).2.1, (hB ρ hb).2.2⟩
  have hs : (∑ ρ ∈ B, DusartSmoothing.RvM.zeroMult ρ) +
      (∑ ρ ∈ A, DusartSmoothing.RvM.zeroMult ρ) ≤
      ∑ ρ ∈ ft.toFinset, DusartSmoothing.RvM.zeroMult ρ := by
    calc
      _ = ∑ ρ ∈ A ∪ B, DusartSmoothing.RvM.zeroMult ρ := by
        rw [Finset.sum_union hd]
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  have he : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t =
      ∑ ρ ∈ B, (DusartSmoothing.RvM.zeroMult ρ : ℝ) := by
    simp [finiteZeroCount, B, primeStep, Finset.sum_filter, mul_ite]
  have hNH : DusartSmoothing.RvM.Ncount 0 H = ∑ ρ ∈ A, DusartSmoothing.RvM.zeroMult ρ := by
    rw [DusartSmoothing.RvM.Ncount_zero_eq_four, DusartSmoothing.RvM.Ncount,
      finsum_mem_eq_finite_toFinset_sum _ fH]
  have hNt : DusartSmoothing.RvM.Ncount 0 t =
      ∑ ρ ∈ ft.toFinset, DusartSmoothing.RvM.zeroMult ρ := by
    rw [DusartSmoothing.RvM.Ncount_zero_eq_four, DusartSmoothing.RvM.Ncount,
      finsum_mem_eq_finite_toFinset_sum _ ft]
  rw [he, hNH, hNt]
  exact_mod_cast hs

private theorem finite_zero_count_increment_bound (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im) :
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      DusartSmoothing.RvM.countingMain t - DusartSmoothing.RvM.countingMain H +
      9 * Real.log (t + 5) + 9 * Real.log (H + 5) + 158 := by
  have hi := finite_zero_count_increment Z hZ H t hH hHt hγ
  have ht := (abs_le.mp (DusartSmoothing.RvM.positive_zero_count_error t (hH.trans hHt))).2
  have hH' := (abs_le.mp (DusartSmoothing.RvM.positive_zero_count_error H hH)).1
  linarith only [hi, ht, hH']

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t +
      (DusartSmoothing.RvM.Ncount 0 H : ℝ) ≤ (DusartSmoothing.RvM.Ncount 0 t : ℝ)
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (H t : ℝ) (hH : 4 ≤ H) (hHt : H ≤ t) (hγ : ∀ ρ ∈ Z, H < ρ.im),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      DusartSmoothing.RvM.countingMain t - DusartSmoothing.RvM.countingMain H +
      9 * Real.log (t + 5) + 9 * Real.log (H + 5) + 158
) := by
  exact ⟨finite_zero_count_increment, finite_zero_count_increment_bound⟩
