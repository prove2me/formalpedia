-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T13:01:43.684764+00:00
-- url     : https://prove2.me/submissions/afbd8485-7b01-43d9-8ee2-5dbee2749e89

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

open MeasureTheory

set_option autoImplicit false

namespace FSL21
open FriendlyShadow.Gaussian

lemma L_nonneg {d : ℕ} (hd : 3 ≤ d) (μ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : LogLipschitz μ L) : 0 ≤ L := by
  obtain ⟨hpos, hlip⟩ := hL
  set x : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, by omega⟩ 1 with hxdef
  have hx : ‖x - 0‖ = 1 := by simp [hxdef]
  have h1 := hlip x 0
  have h2 := hlip 0 x
  rw [hx] at h1
  rw [norm_sub_rev, hx] at h2
  have hpx := hpos x
  have h3 : μ x ≤ Real.exp (L * 1) * (Real.exp (L * 1) * μ x) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  rw [← mul_assoc, ← Real.exp_add] at h3
  by_contra hneg
  push Not at hneg
  have h4 : Real.exp (L * 1 + L * 1) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_zero] at h4
  have := mul_lt_mul_of_pos_right h4 hpx
  linarith

end FSL21

open MeasureTheory FriendlyShadow.Gaussian RealInnerProductSpace ENNReal in
theorem solution {d : ℕ} (hd : 3 ≤ d) (μ : EuclideanSpace ℝ (Fin d) → ℝ) (hμ : IsDensity μ)
    (y : EuclideanSpace ℝ (Fin d)) (hy : HasMean μ y) (L : ℝ) (hL : LogLipschitz μ L)
    (R : ℝ) (hR : CutoffRadiusLE μ y (1 / 2) R) :
    (d : ℝ) / 3 ≤ L * R := by
  classical
  have hL0 := FSL21.L_nonneg hd μ L hL
  obtain ⟨hμ0, hμint, hμ1⟩ := hμ
  obtain ⟨hpos, hlip⟩ := hL
  have hfint : Integrable (fun u => μ (y + u)) := hμint.comp_add_left y
  have hf1 : ∫ u, μ (y + u) = 1 := by
    rw [integral_add_left_eq_self (fun x => μ x) y]; exact hμ1
  set Bl : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 R with hBl
  have hBlm : MeasurableSet Bl := measurableSet_ball
  -- mass of the ball ≥ 1/2
  set S : Set (EuclideanSpace ℝ (Fin d)) := {x | R ≤ ‖x - y‖} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const (continuous_norm.comp (continuous_id.sub continuous_const)).measurable
  have hSint : ∫ x in S, μ x ≤ 1 / 2 := by
    have h := hR
    unfold CutoffRadiusLE densityMeasure at h
    rw [withDensity_apply _ hSm, ← ofReal_integral_eq_lintegral_ofReal hμint.integrableOn
      (Filter.Eventually.of_forall (fun x => hμ0 x))] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h
  have hpt : ∀ u, S.indicator μ (y + u) = Blᶜ.indicator (fun u => μ (y + u)) u := by
    intro u
    have e : (y + u ∈ S) ↔ (u ∈ Blᶜ) := by
      simp only [hSdef, hBl, Set.mem_setOf_eq, add_sub_cancel_left, Set.mem_compl_iff,
        Metric.mem_ball, dist_zero_right, not_lt]
    by_cases h : u ∈ Blᶜ
    · rw [Set.indicator_of_mem (e.mpr h), Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (fun h' => h (e.mp h')), Set.indicator_of_notMem h]
  have hcomp : ∫ u, Blᶜ.indicator (fun u => μ (y + u)) u ≤ 1 / 2 := by
    rw [← integral_indicator hSm] at hSint
    rw [← integral_add_left_eq_self (S.indicator μ) y] at hSint
    simpa only [hpt] using hSint
  have hB : 1 / 2 ≤ ∫ u, Bl.indicator (fun u => μ (y + u)) u := by
    have hsum : (∫ u, Bl.indicator (fun u => μ (y + u)) u) +
        ∫ u, Blᶜ.indicator (fun u => μ (y + u)) u = 1 := by
      rw [← integral_add (hfint.indicator hBlm) (hfint.indicator hBlm.compl)]
      simp only [← Pi.add_apply (Bl.indicator _), Set.indicator_self_add_compl]
      exact hf1
    linarith
  -- the scaled integral
  set g : EuclideanSpace ℝ (Fin d) → ℝ := (Metric.ball 0 (3 * R)).indicator (fun u => μ (y + u))
    with hg
  have hgint : Integrable g := hfint.indicator measurableSet_ball
  have hg1 : ∫ v, g v ≤ 1 := by
    rw [← hf1]
    refine integral_mono hgint hfint ?_
    exact Set.indicator_le_self' (fun v _ => hμ0 _)
  have hA : (3 : ℝ) ^ d * ∫ u, g ((3 : ℝ) • u) ≤ 1 := by
    rw [Measure.integral_comp_smul_of_nonneg volume g (3 : ℝ) (hR := by norm_num), finrank_euclideanSpace_fin, smul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    exact hg1
  have hAint : Integrable (fun u => g ((3 : ℝ) • u)) := hgint.comp_smul (by norm_num)
  have hAB : Real.exp (-(2 * L * R)) * ∫ u, Bl.indicator (fun u => μ (y + u)) u ≤
      ∫ u, g ((3 : ℝ) • u) := by
    rw [← integral_const_mul]
    refine integral_mono ((hfint.indicator hBlm).const_mul _) hAint (fun u => ?_)
    by_cases hu : u ∈ Bl
    · have hu' : ‖u‖ < R := by simpa [hBl] using hu
      have h3u : (3 : ℝ) • u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (3 * R) := by
        simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by norm_num : (0:ℝ) < 3)]; linarith
      simp only [hg]
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem h3u]
      have hl := hlip (y + u) (y + (3 : ℝ) • u)
      have e : (y + u) - (y + (3 : ℝ) • u) = (-2 : ℝ) • u := by module
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_neg (by norm_num : (-2:ℝ) < 0)] at hl
      have hexp : Real.exp (L * (-(-2) * ‖u‖)) ≤ Real.exp (2 * L * R) := by
        apply Real.exp_le_exp.mpr
        nlinarith [norm_nonneg u]
      have hp3 := hpos (y + (3 : ℝ) • u)
      have h5 : μ (y + u) ≤ Real.exp (2 * L * R) * μ (y + (3 : ℝ) • u) :=
        hl.trans (mul_le_mul_of_nonneg_right hexp hp3.le)
      have h6 : Real.exp (-(2 * L * R)) * Real.exp (2 * L * R) = 1 := by
        rw [← Real.exp_add]; simp
      calc Real.exp (-(2 * L * R)) * μ (y + u)
          ≤ Real.exp (-(2 * L * R)) * (Real.exp (2 * L * R) * μ (y + (3 : ℝ) • u)) :=
            mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
        _ = μ (y + (3 : ℝ) • u) := by rw [← mul_assoc, h6, one_mul]
    · rw [Set.indicator_of_notMem hu, mul_zero]
      exact Set.indicator_nonneg (fun v _ => hμ0 _) _
  -- combine: 3^d ≤ 2 exp(2LR)
  set X := Real.exp (2 * L * R) with hX
  have hXpos : 0 < X := Real.exp_pos _
  have hkey : (3 : ℝ) ^ d * (X⁻¹ * (1 / 2)) ≤ 1 := by
    have h1 : X⁻¹ * (1 / 2) ≤ ∫ u, g ((3 : ℝ) • u) := by
      rw [hX, ← Real.exp_neg]
      exact (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le).trans hAB
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans hA
  have h3X : (3 : ℝ) ^ d ≤ 2 * X := by
    have e : (3 : ℝ) ^ d = (3 : ℝ) ^ d * (X⁻¹ * (1 / 2)) * (2 * X) := by
      field_simp
    rw [e]
    calc (3 : ℝ) ^ d * (X⁻¹ * (1 / 2)) * (2 * X) ≤ 1 * (2 * X) :=
          mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = 2 * X := one_mul _
  by_contra hlt
  push Not at hlt
  set E := Real.exp (2 / 3) with hE
  have hXE : X < E ^ d := by
    rw [hX, hE, ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    linarith
  have hE2 : E < 2 := by
    rw [hE, ← Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.log_two_gt_d9
    linarith
  have hE0 : 0 < E := Real.exp_pos _
  have h6 : (27 / 8 : ℝ) ≤ (3 / 2) ^ d := by
    calc (27 / 8 : ℝ) = (3 / 2) ^ 3 := by norm_num
      _ ≤ (3 / 2) ^ d := pow_le_pow_right₀ (by norm_num) hd
  have h5 : (27 / 8 : ℝ) * E ^ d ≤ (3 : ℝ) ^ d := by
    calc (27 / 8 : ℝ) * E ^ d ≤ (3 / 2) ^ d * E ^ d :=
          mul_le_mul_of_nonneg_right h6 (pow_nonneg hE0.le _)
      _ = (3 / 2 * E) ^ d := (mul_pow _ _ _).symm
      _ ≤ 3 ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
  have hEd : 0 < E ^ d := pow_pos hE0 d
  linarith
