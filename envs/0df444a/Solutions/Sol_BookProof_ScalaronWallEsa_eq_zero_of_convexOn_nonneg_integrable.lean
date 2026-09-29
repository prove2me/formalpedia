-- Prove2me | solution 1 for BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-17T12:56:20.174911+00:00
-- url     : https://prove2.me/submissions/8ea84050-e82a-4817-bc63-9925c49f3d23

-- Generated from ChapterScalaronWallEsa.lean — solution of BookProof.ScalaronWallEsa.eq_zero_of_convexOn_nonneg_integrable
import Mathlib
import Definitions.Def_ChapterScalaronWallEsa
open BookProof.ScalaronWallEsa













open MeasureTheory SchwartzMap Set
open BookProof.FarisLavine BookProof.StrichartzWave BookProof.ScalaronEsa
open BookProof.Starobinsky BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent
open BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {F : ℝ → ℝ} (hconv : ConvexOn ℝ univ F)
    (hnn : ∀ x, 0 ≤ F x) (hint : Integrable F volume) (a : ℝ) : F a = 0 := by

  by_contra hne
  have hpos : 0 < F a := lt_of_le_of_ne (hnn a) (Ne.symm hne)
  set C := ∫ x, F x with hCdef
  have hC0 : 0 ≤ C := integral_nonneg fun x => hnn x
  have hmid : ∀ s : ℝ, 2 * F a ≤ F (a - s) + F (a + s) := by
    intro s
    have h := hconv.2 (mem_univ (a - s)) (mem_univ (a + s)) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simp only [smul_eq_mul] at h
    have hmid' : (1/2 : ℝ) * (a - s) + (1/2) * (a + s) = a := by ring
    rw [hmid'] at h
    linarith
  have hkey : ∀ R : ℝ, 0 < R → 2 * F a * R ≤ C := by
    intro R hR
    have hi1 : IntervalIntegrable (fun s => F (a - s)) volume 0 R :=
      (hint.comp_sub_left a).intervalIntegrable
    have hi2 : IntervalIntegrable (fun s => F (a + s)) volume 0 R :=
      (hint.comp_add_left a).intervalIntegrable
    have hmono : ∫ s in (0:ℝ)..R, (2 * F a) ≤ ∫ s in (0:ℝ)..R, (F (a - s) + F (a + s)) :=
      intervalIntegral.integral_mono_on hR.le _root_.intervalIntegrable_const (hi1.add hi2)
        (fun s _ => hmid s)
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_comp_sub_left F a,
      intervalIntegral.integral_comp_add_left F a] at hmono
    simp only [sub_zero, add_zero, intervalIntegral.integral_const, smul_eq_mul] at hmono
    have hadj : (∫ x in (a - R)..a, F x) + ∫ x in a..(a + R), F x = ∫ x in (a-R)..(a+R), F x :=
      intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
        hint.intervalIntegrable
    rw [hadj] at hmono
    have hle : (∫ x in (a-R)..(a+R), F x) ≤ C := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun x => hnn x)
    nlinarith
  have h2 := hkey ((C + 1) / (2 * F a)) (by positivity)
  rw [mul_div_cancel₀] at h2
  · linarith
  · positivity
