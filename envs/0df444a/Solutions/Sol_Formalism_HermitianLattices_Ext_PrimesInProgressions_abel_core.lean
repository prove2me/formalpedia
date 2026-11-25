-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.abel_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:19:42.456806+00:00
-- url     : https://prove2.me/submissions/f1ee7ac3-cdf4-4478-947c-e2e3ec2e54f6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abel_log
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_sum_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_Fm_div_mul_log_sq
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Fm_parts
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Fm_abs_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_liX_two_rpow_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcΛ : ∀ n, c n ≤ ArithmeticFunction.vonMangoldt n)
    {K θ β D X : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hD : 0 ≤ D)
    (h : ∀ t, √X ≤ t → t ≤ X → |(∑ n ∈ Icc 0 ⌊t⌋₊, c n) - Fm K θ β t| ≤ D * t) :
    |∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β))| ≤
      5 * D * X / Real.log X + 40 * √X := by
  have h0 : c 0 = 0 := le_antisymm (by simpa using hcΛ 0) (hc0 0)
  have h1 : c 1 = 0 := le_antisymm (by simpa using hcΛ 1) (hc0 1)
  have hX2 : 2 ≤ X := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hs4 : 4 ≤ √X := by rw [Real.le_sqrt' (by norm_num)]; linarith
  have hss : √X * √X = X := Real.mul_self_sqrt (by linarith)
  have hsX : √X ≤ X := by nlinarith
  have hL : 1 ≤ Real.log X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hX
    linarith
  have hL0 : 0 < Real.log X := by linarith
  have habel := abel_log c h0 h1 hX2
  have hparts := Fm_parts K θ (by linarith : 0 < β) hX2
  set Ψ : ℝ → ℝ := fun t => ∑ n ∈ Icc 0 ⌊t⌋₊, c n with hΨ
  set g : ℝ → ℝ := fun t => Ψ t / (t * Real.log t ^ 2) - Fm K θ β t / (t * Real.log t ^ 2) with hg
  have hgi : ∀ a b : ℝ, 2 ≤ a → a ≤ b → IntervalIntegrable g MeasureTheory.volume a b := fun a b ha hab =>
    (intervalIntegrable_sum_div c ha hab).sub (intervalIntegrable_Fm_div_mul_log_sq K θ β ha hab)
  have hI : ∫ t in (2 : ℝ)..X, g t = (∫ t in (2 : ℝ)..X, Ψ t / (t * Real.log t ^ 2)) -
      ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) :=
    intervalIntegral.integral_sub (intervalIntegrable_sum_div c le_rfl hX2) (intervalIntegrable_Fm_div_mul_log_sq K θ β le_rfl hX2)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi 2 (√X) le_rfl (by linarith))
    (hgi (√X) X (by linarith) hsX)
  have hΨle : ∀ t : ℝ, 0 ≤ t → |Ψ t| ≤ 6 * t := by
    intro t ht
    have hn : 0 ≤ Ψ t := Finset.sum_nonneg (fun n _ => hc0 n)
    rw [abs_of_nonneg hn]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    calc Ψ t ≤ ∑ n ∈ Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt n := Finset.sum_le_sum (fun n _ => hcΛ n)
      _ = Chebyshev.psi t := (Chebyshev.psi_eq_sum_Icc t).symm
      _ ≤ (Real.log 4 + 4) * t := Chebyshev.psi_le_const_mul_self ht
      _ ≤ 6 * t := by gcongr; linarith
  have hI1 : |∫ t in (2 : ℝ)..√X, g t| ≤ 36 * |√X - 2| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht2 : 2 < t := ht.1
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2.le
    have hsq : 1 / 4 ≤ Real.log t ^ 2 := by nlinarith
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    have ha := hΨle t (by linarith)
    have hb := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by linarith : 1 ≤ t)
    rw [Real.norm_eq_abs, hg]
    simp only []
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have hab : |Ψ t - Fm K θ β t| ≤ 9 * t := by
      rw [abs_le] at ha hb ⊢
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    nlinarith
  have hI2 : |∫ t in (√X)..X, g t| ≤ 4 * D / Real.log X ^ 2 * |X - √X| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le hsX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hlt : Real.log X / 2 ≤ Real.log t := by
      rw [← Real.log_sqrt (by linarith)]
      exact Real.log_le_log (by linarith) ht.1.le
    have hlt0 : 0 < Real.log t := by linarith
    have hsq : Real.log X ^ 2 ≤ 4 * Real.log t ^ 2 := by nlinarith
    have hpos : 0 < t * Real.log t ^ 2 := by positivity
    rw [Real.norm_eq_abs, hg]
    simp only []
    rw [← sub_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc |Ψ t - Fm K θ β t| * Real.log X ^ 2 ≤ (D * t) * (4 * Real.log t ^ 2) := by
          gcongr
          exact h t ht.1.le ht.2
      _ = 4 * D * (t * Real.log t ^ 2) := by ring
  have heq : ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n - K * (liX X - θ * liX (X ^ β)) =
      (Ψ X - Fm K θ β X) / Real.log X + ((∫ t in (2 : ℝ)..√X, g t) + ∫ t in (√X)..X, g t) +
        Fm K θ β 2 / Real.log 2 + K * θ * liX ((2 : ℝ) ^ β) := by
    have e1 : K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) =
        K * (liX X - θ * liX (X ^ β)) + K * θ * liX ((2 : ℝ) ^ β) := by ring
    have e2 : (Ψ X - Fm K θ β X) / Real.log X = Ψ X / Real.log X - Fm K θ β X / Real.log X := sub_div _ _ _
    linarith [habel, hparts, hI, hsplit]
  have b1 : |(Ψ X - Fm K θ β X) / Real.log X| ≤ D * X / Real.log X := by
    rw [abs_div, abs_of_pos hL0]
    gcongr
    exact h X hsX le_rfl
  have b2 : |Fm K θ β 2 / Real.log 2| ≤ 12 := by
    have := Fm_abs_le hK0 hK1 hθ hβ hβ1 (by norm_num : (1 : ℝ) ≤ 2)
    rw [abs_div, abs_of_pos (by linarith : 0 < Real.log 2), div_le_iff₀ (by linarith)]
    linarith
  have b3 : |K * θ * liX ((2 : ℝ) ^ β)| ≤ 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hK0]
    calc K * |θ| * |liX ((2 : ℝ) ^ β)| ≤ 1 * 1 * 4 := by
          gcongr
          exact liX_two_rpow_abs hβ hβ1
      _ = 4 := by norm_num
  have b4 : 4 * D / Real.log X ^ 2 * |X - √X| ≤ 4 * (D * X / Real.log X) := by
    rw [abs_of_nonneg (by linarith)]
    have hDX : 0 ≤ D * X := by positivity
    have : D * X / Real.log X ^ 2 ≤ D * X / Real.log X := by
      apply div_le_div_of_nonneg_left hDX hL0
      nlinarith
    calc 4 * D / Real.log X ^ 2 * (X - √X) ≤ 4 * D / Real.log X ^ 2 * X := by
          gcongr
          linarith
      _ = 4 * (D * X / Real.log X ^ 2) := by ring
      _ ≤ _ := by linarith
  have b5 : 36 * |√X - 2| ≤ 36 * √X - 72 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  rw [heq]
  have e5 : 5 * D * X / Real.log X = 5 * (D * X / Real.log X) := by ring
  rw [e5]
  rw [abs_le] at *
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, hI1.1, hI1.2, hI2.1, hI2.2]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
