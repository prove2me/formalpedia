-- Prove2me | solution 1 for FirstPassageLinearTransport.threeQuarterLowerTailMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:25.87989+00:00
-- url     : https://prove2.me/submissions/50925232-1647-44f6-969e-723a5d514359

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_sum_threeQuarter_centered_sq
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {eps : ℝ} (heps : 0 < eps) {r : ℕ} (hr : 0 < r) :
    threeQuarterLowerTailMass eps r ≤
      3 / (16 * eps ^ 2 * (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoef : 0 < eps ^ 2 * (r : ℝ) ^ 2 := by positivity
  have hweighted : eps ^ 2 * (r : ℝ) ^ 2 *
        threeQuarterLowerTailMass eps r ≤
      ∑ v : Fin r → Bool,
        bernoulliWordWeight (3 / 4) v *
          (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 := by
    classical
    unfold threeQuarterLowerTailMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _hv
    have hw : 0 ≤ bernoulliWordWeight (3 / 4) v :=
      bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v
    by_cases hv : ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r
    · simp only [hv, if_true, mul_one]
      have hdev :
          ((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4 ≤
            -(eps * (r : ℝ)) := by
        linarith
      have hsq : eps ^ 2 * (r : ℝ) ^ 2 ≤
          (((boolSupport v).card : ℝ) - 3 * (r : ℝ) / 4) ^ 2 := by
        nlinarith [mul_pos heps hrR]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hsq)]
    · simp only [hv, if_false, mul_zero, mul_zero]
      exact mul_nonneg hw (sq_nonneg _)
  rw [sum_threeQuarter_centered_sq] at hweighted
  have hquot : 3 / (16 * eps ^ 2 * (r : ℝ)) =
      (3 * (r : ℝ) / 16) / (eps ^ 2 * (r : ℝ) ^ 2) := by
    field_simp
  rw [hquot]
  apply (le_div_iff₀ hcoef).2
  calc
    threeQuarterLowerTailMass eps r *
        (eps ^ 2 * (r : ℝ) ^ 2) =
        eps ^ 2 * (r : ℝ) ^ 2 *
          threeQuarterLowerTailMass eps r := by ring
    _ ≤ 3 * (r : ℝ) / 16 := hweighted
end FirstPassageLinearTransport
