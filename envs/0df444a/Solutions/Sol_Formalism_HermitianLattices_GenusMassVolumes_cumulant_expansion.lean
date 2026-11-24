-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.cumulant_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:45.819839+00:00
-- url     : https://prove2.me/submissions/f59d60a6-05af-4a24-842f-f678ab139a8e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightShiftProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
private lemma exp_quadratic_lower_bound {y ε : ℝ} (hε1 : ε ≤ 1) (hy : |y| ≤ ε) :
    1 + y + y ^ 2 / 2 * (1 - 4 * ε / 9) ≤ Real.exp y := by
  have hy1 : |y| ≤ 1 := hy.trans hε1
  have hb := Real.exp_bound hy1 (n := 3) (by norm_num)
  have hsum : ∑ m ∈ range 3, y ^ m / (m.factorial : ℝ) = 1 + y + y ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have hc : |y| ^ 3 * (((3 : ℕ).succ : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℕ))) = |y| ^ 3 * (2 / 9) := by
    norm_num [Nat.factorial]
  rw [hc] at hb
  have h3 : |y| ^ 3 ≤ y ^ 2 * ε := by
    have : |y| ^ 3 = y ^ 2 * |y| := by rw [← sq_abs y]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hy (sq_nonneg y)
  have := (abs_le.mp hb).1
  nlinarith
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : CumulantLowerBound := by
  intro ι _ P y ε hP hP1 hmean hε0 hε1 hy
  set V : ℝ := ∑ j, P j * y j ^ 2 with hV
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun j _ => mul_nonneg (hP j) (sq_nonneg _)
  have hVε : V ≤ ε ^ 2 := by
    calc V ≤ ∑ j, P j * ε ^ 2 := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hP j)
          exact sq_le_sq' (by linarith [(abs_le.mp (hy j)).1]) (abs_le.mp (hy j)).2
      _ = ε ^ 2 := by rw [← Finset.sum_mul, hP1, one_mul]
  set z : ℝ := V / 2 * (1 - 4 * ε / 9) with hz
  have hS : 1 + z ≤ ∑ j, P j * Real.exp (y j) := by
    calc 1 + z = ∑ j, P j * (1 + y j + y j ^ 2 / 2 * (1 - 4 * ε / 9)) := by
          have : ∀ j, P j * (1 + y j + y j ^ 2 / 2 * (1 - 4 * ε / 9)) =
              P j + P j * y j + (P j * y j ^ 2) * ((1 - 4 * ε / 9) / 2) := fun j => by ring
          simp only [this]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hP1, hmean, ← hV, hz]
          ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (exp_quadratic_lower_bound hε1 (hy j)) (hP j)
  have hc0 : 0 ≤ 1 - 4 * ε / 9 := by linarith
  have hz0 : 0 ≤ z := mul_nonneg (by linarith) hc0
  have h1z : 0 < 1 + z := by linarith
  have hlog : Real.log (1 + z) ≤ Real.log (∑ j, P j * Real.exp (y j)) := Real.log_le_log h1z hS
  have hinv := Real.one_sub_inv_le_log_of_pos h1z
  have hzz : z * (1 - z) ≤ 1 - (1 + z)⁻¹ := by
    have : 1 - (1 + z)⁻¹ = z / (1 + z) := by field_simp; ring
    rw [this, le_div_iff₀ h1z]
    nlinarith [mul_nonneg hz0 (mul_nonneg hz0 hz0)]
  have hzV : z ≤ ε / 2 := by
    have h1 : z ≤ V / 2 := by
      rw [hz]; nlinarith
    have h2 : ε ^ 2 ≤ ε := by nlinarith
    linarith
  have hfin : V / 2 * (1 - ε) ≤ z * (1 - z) := by
    have h1 : z * (1 - ε / 2) ≤ z * (1 - z) := mul_le_mul_of_nonneg_left (by linarith) hz0
    have h2 : V / 2 * (1 - ε) ≤ z * (1 - ε / 2) := by
      rw [hz, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith [mul_nonneg hε0 hε0]
    linarith
  linarith
end Formalism.HermitianLattices.GenusMassVolumes
