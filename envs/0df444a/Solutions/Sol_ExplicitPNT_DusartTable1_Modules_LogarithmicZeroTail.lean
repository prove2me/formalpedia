-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.LogarithmicZeroTail
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:30:37.182209+00:00
-- url     : https://prove2.me/submissions/70a2a35e-36ae-465c-bc64-0639f957ed68

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
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_LogarithmicZeroCount

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex Set MeasureTheory
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem finite_count_integrable : ∀ (Z : Finset ℂ) (a b : ℝ),
    IntervalIntegrable (finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im) volume a b :=
  ExplicitPNT.DusartTable1.Modules.PowerQuarterAbel.1

private theorem finite_zero_count_log_fifth : ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (t : ℝ) (ht : 1000 ≤ t),
    finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤
      (1 / 5 : ℝ) * t * Real.log t :=
  ExplicitPNT.DusartTable1.Modules.LogarithmicZeroCount.2.2.1

private theorem finite_log_inverse_cube_tail (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a C : ℝ) (ha : 100 ≤ a) (hC : 0 ≤ C)
    (hcount : ∀ t : ℝ, a ≤ t →
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ C * t * Real.log t)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 * C / 2) * Real.log a + 3 * C / 4) / a^2 := by
  classical
  by_cases hn : Z.Nonempty
  · let b : ℝ := max a (Z.sup' hn Complex.im)
    have hab : a ≤ b := le_max_left _ _
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := ha0.trans_le hab
    have hγb (ρ : ℂ) (hρ : ρ ∈ Z) : ρ.im ≤ b :=
      (Finset.le_sup' Complex.im hρ).trans (le_max_right _ _)
    let g : ℝ → ℝ := fun t => 1 / t^3
    let d : ℝ → ℝ := fun t => -3 / t^4
    let J : ℝ → ℝ := fun t => ((3 * C / 2) * Real.log t + 3 * C / 4) / t^2
    have hcont : ContinuousOn d (Icc a b) := by
      intro t ht
      have ht0 : 0 < t := ha0.trans_le ht.1
      apply ContinuousAt.continuousWithinAt
      dsimp [d]
      fun_prop (disch := positivity)
    have hd : ∀ t ∈ Icc a b, HasDerivAt g (d t) t := by
      intro t ht
      have hn : t ≠ 0 := (ha0.trans_le ht.1).ne'
      have h := ((hasDerivAt_id t).pow 3).inv (pow_ne_zero 3 hn)
      have he : (id ^ 3 : ℝ → ℝ)⁻¹ = g := by funext u; simp [g]
      rw [he] at h
      exact h.congr_deriv (by dsimp [d]; field_simp [hn] <;> ring)
    have hJ : ∀ t ∈ uIcc a b,
        HasDerivAt J ((C * t * Real.log t) * d t) t := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      have hn : t ≠ 0 := (ha0.trans_le ht.1).ne'
      have h := ((((Real.hasDerivAt_log hn).const_mul (3 * C / 2)).add_const (3 * C / 4)).div
        ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 hn))
      apply h.congr_deriv
      dsimp [d]
      field_simp [hn]
      ring
    have hc : ContinuousOn (fun t => C * t * Real.log t) (Icc a b) := by
      intro t ht
      have hn : t ≠ 0 := (ha0.trans_le ht.1).ne'
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    have himaj : IntervalIntegrable (fun t => (C * t * Real.log t) * d t) volume a b := by
      have hc' : ContinuousOn (fun t => (C * t * Real.log t) * d t) (uIcc a b) := by
        intro t ht
        rw [uIcc_of_le hab] at ht
        have ht0 : 0 < t := ha0.trans_le ht.1
        have hn : t ≠ 0 := (ha0.trans_le ht.1).ne'
        apply ContinuousAt.continuousWithinAt
        dsimp [d]
        fun_prop (disch := positivity)
      exact hc'.intervalIntegrable
    have hi : IntervalIntegrable
        (fun t => finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t) volume a b :=
      (finite_count_integrable Z a b).mul_continuousOn (by simpa [uIcc_of_le hab] using hcont)
    have hile : (∫ t in a..b, (C * t * Real.log t) * d t) ≤
        ∫ t in a..b, finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t * d t := by
      apply intervalIntegral.integral_mono_on hab himaj hi
      intro t ht
      apply mul_le_mul_of_nonpos_right (hcount t ht.1)
      dsimp [d]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    have hival : (∫ t in a..b, (C * t * Real.log t) * d t) = J b - J a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hJ himaj
    have hQb : finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im b =
        ∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      simp [primeStep, hγb ρ hρ]
    have hcb := hcount b hab
    rw [hQb] at hcb
    have hterm : g b * (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ)) ≤
        C * Real.log b / b^2 := by
      calc
        _ ≤ g b * (C * b * Real.log b) :=
          mul_le_mul_of_nonneg_left hcb (by dsimp [g]; positivity)
        _ = _ := by dsimp [g]; field_simp [hb0.ne'] <;> ring
    have hJb : C * Real.log b / b^2 ≤ J b := by
      dsimp [J]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hlog : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
      nlinarith
    have he := finite_zero_summation_by_parts Z DusartSmoothing.RvM.zeroMult Complex.im
      a b hab (fun ρ hρ => ⟨hγ ρ hρ, hγb ρ hρ⟩) g d hcont hd
    change (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * g ρ.im) ≤ J a
    rw [he]
    rw [hival] at hile
    linarith
  · have he : Z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, Finset.sum_empty]
    have hl : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
    positivity

private theorem finite_positive_inverse_cube_tail_log (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 1000 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im) :
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2 := by
  have hh := finite_log_inverse_cube_tail Z hZ T (1 / 5) (by linarith) (by norm_num)
    (fun t ht => finite_zero_count_log_fifth Z hZ t (hT.trans ht)) hγ
  norm_num at hh ⊢
  exact hh

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (a C : ℝ) (ha : 100 ≤ a) (hC : 0 ≤ C)
    (hcount : ∀ t : ℝ, a ≤ t →
      finiteZeroCount Z DusartSmoothing.RvM.zeroMult Complex.im t ≤ C * t * Real.log t)
    (hγ : ∀ ρ ∈ Z, a ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 * C / 2) * Real.log a + 3 * C / 4) / a^2
) ∧
(
    ∀ (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, DusartSmoothing.RvM.IsNontrivialZero ρ ∧ 0 < ρ.im)
    (T : ℝ) (hT : 1000 ≤ T) (hγ : ∀ ρ ∈ Z, T ≤ ρ.im),
    (∑ ρ ∈ Z, (DusartSmoothing.RvM.zeroMult ρ : ℝ) * (1 / ρ.im^3)) ≤
      ((3 / 10 : ℝ) * Real.log T + 3 / 20) / T^2
) := by
  exact ⟨finite_log_inverse_cube_tail, finite_positive_inverse_cube_tail_log⟩
