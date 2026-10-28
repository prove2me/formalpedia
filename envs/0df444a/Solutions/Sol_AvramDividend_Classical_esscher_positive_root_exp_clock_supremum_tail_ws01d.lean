-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_exp_clock_supremum_tail_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:52:54.141533+00:00
-- url     : https://prove2.me/submissions/28234ac5-02d0-4625-b641-5ed8f4c0544a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (phi q : ℝ) (hphi : 0 < phi) (hq : 0 < q) (hroot : X.ψ phi = q)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (phi + lam) - q = p)
    (b : ℝ) (hb : 0 < b) :
    ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q))))
      {z : Ω × ℝ | b < runningSup X z.2.toNNReal z.1} =
      ENNReal.ofReal (Real.exp (-(lam * b))) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let μ := P.prod (ProbabilityTheory.expMeasure p)
  let T : Ω → ℝ≥0∞ := fun ω => twoSidedExitUpTime X b ω
  let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let L : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q))
  let S : Set (Ω × ℝ) := {z | b < runningSup X z.2.toNNReal z.1}
  let B : Set (Ω × ℝ) := {z | T z.1 < (⊤ : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2}
  have hT : Measurable T := chat08_upper_passage_clock_measurable X b
  have hAge : Measurable age := ENNReal.measurable_toNNReal.comp hT
  have hS : MeasurableSet S := by
    dsimp [S]; exact measurableSet_lt measurable_const (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hTie : μ {z : Ω × ℝ | (age z.1 : ℝ) = z.2} = 0 := by
    let E : Set (Ω × ℝ) := {z | (age z.1 : ℝ) = z.2}
    have hE : MeasurableSet E := measurableSet_eq_fun (hAge.coe_nnreal_real.comp measurable_fst) measurable_snd
    change μ E = 0
    rw [Measure.prod_apply hE]
    have hsection (ω : Ω) : ProbabilityTheory.expMeasure p (Prod.mk ω ⁻¹' E) = 0 := by
      have heq : Prod.mk ω ⁻¹' E = {(age ω : ℝ)} := by ext t; simp [E, eq_comm]
      rw [heq]
      change (volume.withDensity (ProbabilityTheory.exponentialPDF p)) {(age ω : ℝ)} = 0
      exact (withDensity_absolutelyContinuous volume (ProbabilityTheory.exponentialPDF p)) (by simp)
    simp only [hsection, MeasureTheory.lintegral_zero]
  have hEvent (z : Ω × ℝ) (hne : (age z.1 : ℝ) ≠ z.2) :
      z ∈ S ↔ z ∈ B := by
    have hpass := avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon X b (le_of_lt hb) z.1 z.2.toNNReal
    change b < runningSup X z.2.toNNReal z.1 ↔ T z.1 < (z.2.toNNReal : ℝ≥0∞) at hpass
    change (b < runningSup X z.2.toNNReal z.1) ↔ (T z.1 < (⊤ : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2)
    rw [hpass]
    by_cases hneg : z.2 < 0
    · have hzero : z.2.toNNReal = 0 := Real.toNNReal_of_nonpos (le_of_lt hneg)
      rw [hzero]
      constructor
      · intro h; exact ((not_lt_of_ge bot_le) h).elim
      · intro h; exact ((not_le_of_gt hneg) (le_trans (age z.1).property h.2)).elim
    · have ht : 0 ≤ z.2 := le_of_not_gt hneg
      have htime : (z.2.toNNReal : ℝ) = z.2 := Real.coe_toNNReal _ ht
      by_cases hfin : T z.1 = (⊤ : ℝ≥0∞)
      · simp [hfin]
      · have hconvert :
            (T z.1 < (z.2.toNNReal : ℝ≥0∞)) ↔ (age z.1 : ℝ) < z.2 := by
          constructor
          · intro h
            have hh : age z.1 < z.2.toNNReal := by
              apply ENNReal.coe_lt_coe.mp
              simpa only [age, ENNReal.coe_toNNReal hfin] using h
            have hr : (age z.1 : ℝ) < (z.2.toNNReal : ℝ) := by exact_mod_cast hh
            simpa only [htime] using hr
          · intro h
            have hr : (age z.1 : ℝ) < (z.2.toNNReal : ℝ) := by simpa only [htime] using h
            have hh : age z.1 < z.2.toNNReal := by exact_mod_cast hr
            have hco : ((age z.1 : ℝ≥0) : ℝ≥0∞) < (z.2.toNNReal : ℝ≥0∞) := by exact_mod_cast hh
            simpa only [age, ENNReal.coe_toNNReal hfin] using hco
        rw [hconvert]
        have hfinite : T z.1 < (⊤ : ℝ≥0∞) := lt_top_iff_ne_top.mpr hfin
        simp only [hfinite, true_and]
        exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩
  have hae : (fun z : Ω × ℝ => if z ∈ S then L z else 0) =ᵐ[μ]
      (fun z : Ω × ℝ => if z ∈ B then L z else 0) := by
    apply (ae_iff).2
    have hsub : {z | (if z ∈ S then L z else 0) ≠ (if z ∈ B then L z else 0)} ⊆
      {z : Ω × ℝ | (age z.1 : ℝ) = z.2} := by
      intro z hz
      by_contra hn
      have heq := hEvent z hn
      by_cases hs : z ∈ S
      · have hb : z ∈ B := heq.mp hs
        exact hz (by simp [hs, hb])
      · have hb : z ∉ B := fun hh => hs (heq.mpr hh)
        exact hz (by simp [hs, hb])
    exact le_antisymm ((measure_mono hsub).trans hTie.le) bot_le
  have hbridge :
      (∫⁻ z : Ω × ℝ, if z ∈ B then L z else 0 ∂μ) =
      (∫⁻ ω : Ω, if T ω < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (phi * b - (p + q) * (T ω).toReal))
        else 0 ∂P) := by
    simpa only [B, L, μ, T, age, Set.mem_setOf_eq] using (levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
      X b (le_of_lt hb) p hp phi q (le_of_lt hphi) hroot)
  have hrootShift : X.ψ (phi + lam) = p + q := by linarith
  have hpq : 0 < p + q := add_pos hp hq
  have hfirst :
      (∫⁻ ω : Ω, if T ω < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (-((p + q) * (T ω).toReal))) else 0 ∂P) =
      ENNReal.ofReal (Real.exp (-((phi + lam) * b))) := by
    exact levy_positive_root_exact_strict_upcrossing_discount
      X (p + q) hpq (phi + lam) (add_pos hphi hlam) hrootShift b hb
  have hg : Measurable (fun ω : Ω => if T ω < (⊤ : ℝ≥0∞) then
      ENNReal.ofReal (Real.exp (-((p + q) * (T ω).toReal))) else 0) := by
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (ENNReal.measurable_toReal.comp hT)).neg))).ite
        (measurableSet_lt hT measurable_const) measurable_const
  have hfactor (ω : Ω) :
      (if T ω < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (phi * b - (p + q) * (T ω).toReal)) else 0) =
      ENNReal.ofReal (Real.exp (phi * b)) *
      (if T ω < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (-((p + q) * (T ω).toReal))) else 0) := by
    by_cases h : T ω < (⊤ : ℝ≥0∞)
    · simp only [if_pos h]
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), ← Real.exp_add]
      congr 1
    · simp [h]
  change (μ.withDensity L) S = _
  calc
    (μ.withDensity L) S = (∫⁻ z in S, L z ∂μ) := withDensity_apply L hS
    _ = (∫⁻ z : Ω × ℝ, if z ∈ S then L z else 0 ∂μ) := by rw [← lintegral_indicator hS]; rfl
    _ = (∫⁻ z : Ω × ℝ, if z ∈ B then L z else 0 ∂μ) :=
      lintegral_congr_ae hae
    _ = (∫⁻ ω : Ω, if T ω < (⊤ : ℝ≥0∞) then
          ENNReal.ofReal (Real.exp (phi * b - (p + q) * (T ω).toReal)) else 0 ∂P) := hbridge
    _ = ENNReal.ofReal (Real.exp (phi * b)) *
          (∫⁻ ω : Ω, if T ω < (⊤ : ℝ≥0∞) then
            ENNReal.ofReal (Real.exp (-((p + q) * (T ω).toReal))) else 0 ∂P) := by
      rw [← lintegral_const_mul _ hg]; exact lintegral_congr hfactor
    _ = ENNReal.ofReal (Real.exp (phi * b)) * ENNReal.ofReal (Real.exp (-((phi + lam) * b))) := by rw [hfirst]
    _ = ENNReal.ofReal (Real.exp (-(lam * b))) := by
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)), ← Real.exp_add]
      congr 1; ring
