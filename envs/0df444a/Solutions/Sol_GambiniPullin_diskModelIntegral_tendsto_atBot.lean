-- Prove2me | solution 1 for GambiniPullin.diskModelIntegral_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T18:26:46.123277+00:00
-- url     : https://prove2.me/submissions/b4fb8dce-da15-47c4-b202-82e523d21d2d

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

set_option autoImplicit false

open MeasureTheory GambiniPullin in
lemma gpd_one_le_denom (σ x y : ℝ) (hσ : 0 ≤ σ) : 1 ≤ modelDenom σ x y := by
  unfold modelDenom
  have h1 : 0 < 1 + σ * y ^ 2 := by nlinarith [mul_nonneg hσ (sq_nonneg y)]
  have h2 : 0 ≤ y ^ 2 / (1 + σ * y ^ 2) := div_nonneg (sq_nonneg y) h1.le
  nlinarith [sq_nonneg x]

open MeasureTheory GambiniPullin in
lemma gpd_denom_le (σ x y : ℝ) (hσ : 0 < σ) (hx : x ^ 2 ≤ 1) :
    modelDenom σ x y ≤ 2 + 1 / σ := by
  unfold modelDenom
  have h1 : 0 < 1 + σ * y ^ 2 := by nlinarith [mul_nonneg hσ.le (sq_nonneg y)]
  have h2 : y ^ 2 / (1 + σ * y ^ 2) ≤ 1 / σ := by
    rw [div_le_div_iff₀ h1 hσ]
    nlinarith
  linarith

open MeasureTheory GambiniPullin in
lemma gpd_denom_cont (σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous (fun p : ℝ × ℝ => modelDenom σ p.1 p.2) := by
  unfold modelDenom
  refine Continuous.add (by fun_prop) ?_
  refine Continuous.div (by fun_prop) (by fun_prop) ?_
  intro p
  have := mul_nonneg hσ (sq_nonneg p.2)
  exact (show (0:ℝ) < 1 + σ * p.2 ^ 2 by linarith).ne'

open MeasureTheory in
lemma gpd_int_Icc_one (a b : ℝ) (hab : a ≤ b) : ∫ _x in Set.Icc a b, (1:ℝ) = b - a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  simp

open MeasureTheory in
lemma gpd_int_Icc_sq (a b c : ℝ) (hab : a ≤ b) :
    ∫ y in Set.Icc a b, y ^ 2 / c = (b ^ 3 - a ^ 3) / (3 * c) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_div, integral_pow]
  ring

open MeasureTheory Filter GambiniPullin in
lemma gpd_disk_le (σ : ℝ) (hσ : 0 < σ) (R : ℝ) (hR : 2 ≤ R) :
    diskModelIntegral σ R ≤ 4 * R ^ 2 - R ^ 3 / (6 * (2 + 1 / σ) ^ 2) := by
  set K : ℝ := 2 + 1 / σ with hK
  have hK0 : 0 < K := by positivity
  set D : ℝ × ℝ → ℝ := fun p => modelDenom σ p.1 p.2 with hD
  have hD1 : ∀ p, 1 ≤ D p := fun p => gpd_one_le_denom σ p.1 p.2 hσ.le
  have hDc : Continuous D := gpd_denom_cont σ hσ.le
  have hD2 : ∀ p, D p ^ 2 ≠ 0 := fun p => by
    have := hD1 p
    exact (show (0:ℝ) < D p ^ 2 by positivity).ne'
  set P : ℝ × ℝ → ℝ := fun p => p.1 ^ 2 / D p ^ 2 with hP
  set N : ℝ × ℝ → ℝ := fun p => p.2 ^ 2 / D p ^ 2 with hN
  have hPc : Continuous P := Continuous.div (by fun_prop) (hDc.pow 2) hD2
  have hNc : Continuous N := Continuous.div (by fun_prop) (hDc.pow 2) hD2
  have hsplit : ∀ p : ℝ × ℝ, modelIntegrand σ p.1 p.2 = P p - N p := fun p => by
    simp only [hP, hN, hD, modelIntegrand]
    rw [sub_div]
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2} with hS
  set Q : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc (-R) R with hQ
  set T : Set (ℝ × ℝ) := Set.Icc (-1) 1 ×ˢ Set.Icc (-(R / 2)) (R / 2) with hT
  have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hTc : IsCompact T := isCompact_Icc.prod isCompact_Icc
  have hTm : MeasurableSet T := measurableSet_Icc.prod measurableSet_Icc
  have hQm : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hSQ : S ⊆ Q := by
    intro p hp
    simp only [hS, Set.mem_ofPred_eq] at hp
    simp only [hQ, Set.mem_prod, Set.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  have hTS : T ⊆ S := by
    intro p hp
    simp only [hT, Set.mem_prod, Set.mem_Icc] at hp
    simp only [hS, Set.mem_ofPred_eq]
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hp
    nlinarith
  have hPQ : IntegrableOn P Q := hPc.continuousOn.integrableOn_compact hQc
  have hNQ : IntegrableOn N Q := hNc.continuousOn.integrableOn_compact hQc
  have hPS : IntegrableOn P S := hPQ.mono_set hSQ
  have hNS : IntegrableOn N S := hNQ.mono_set hSQ
  have hNT : IntegrableOn N T := hNS.mono_set hTS
  have h1 : diskModelIntegral σ R = (∫ p in S, P p) - ∫ p in S, N p := by
    rw [← integral_sub hPS hNS]
    show ∫ p in S, modelIntegrand σ p.1 p.2 = _
    congr 1
    funext p
    exact hsplit p
  have hP0 : ∀ p, 0 ≤ P p := fun p => by
    simp only [hP]
    positivity
  have hP1 : ∀ p, P p ≤ 1 := fun p => by
    simp only [hP]
    have h := hD1 p
    have hx : p.1 ^ 2 ≤ D p ^ 2 := by
      have : p.1 ^ 2 + 1 ≤ D p := by
        simp only [hD, modelDenom]
        have h1 : 0 < 1 + σ * p.2 ^ 2 := by nlinarith [mul_nonneg hσ.le (sq_nonneg p.2)]
        have h2 : 0 ≤ p.2 ^ 2 / (1 + σ * p.2 ^ 2) := div_nonneg (sq_nonneg _) h1.le
        linarith
      nlinarith
    rw [div_le_one (by positivity)]
    exact hx
  have h2 : ∫ p in S, P p ≤ ∫ p in Q, P p :=
    setIntegral_mono_set hPQ (ae_of_all _ hP0) hSQ.eventuallyLE
  have h3 : ∫ p in Q, P p ≤ ∫ p in Q, (1:ℝ) :=
    setIntegral_mono_on hPQ (continuous_const.continuousOn.integrableOn_compact hQc) hQm
      (fun p _ => hP1 p)
  have h4 : ∫ p in Q, (1:ℝ) = 4 * R ^ 2 := by
    have := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun _ : ℝ => (1:ℝ)) (fun _ : ℝ => (1:ℝ)) (Set.Icc (-R) R) (Set.Icc (-R) R)
    simp only [mul_one] at this
    rw [hQ, Measure.volume_eq_prod, this, gpd_int_Icc_one _ _ (by linarith)]
    ring
  have hN0 : ∀ p, 0 ≤ N p := fun p => by
    simp only [hN]
    positivity
  have h5 : ∫ p in T, N p ≤ ∫ p in S, N p :=
    setIntegral_mono_set hNS (ae_of_all _ hN0) hTS.eventuallyLE
  have h6 : ∫ p in T, p.2 ^ 2 / K ^ 2 ≤ ∫ p in T, N p := by
    refine setIntegral_mono_on ((by fun_prop : Continuous fun p : ℝ × ℝ => p.2 ^ 2 / K ^ 2
      ).continuousOn.integrableOn_compact hTc) hNT hTm (fun p hp => ?_)
    simp only [hT, Set.mem_prod, Set.mem_Icc] at hp
    have hx : p.1 ^ 2 ≤ 1 := by nlinarith [hp.1.1, hp.1.2]
    have hDK : D p ≤ K := gpd_denom_le σ p.1 p.2 hσ hx
    have hDp := hD1 p
    simp only [hN]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith
  have h7 : ∫ p in T, p.2 ^ 2 / K ^ 2 = R ^ 3 / (6 * K ^ 2) := by
    have := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun _ : ℝ => (1:ℝ)) (fun y : ℝ => y ^ 2 / K ^ 2) (Set.Icc (-1) 1)
      (Set.Icc (-(R / 2)) (R / 2))
    simp only [one_mul] at this
    rw [hT, Measure.volume_eq_prod, this]
    rw [gpd_int_Icc_one _ _ (by norm_num), gpd_int_Icc_sq _ _ _ (by linarith)]
    field_simp
    ring
  rw [h1]
  have := h2.trans h3
  rw [h4] at this
  linarith [h5, h6, h7]

open MeasureTheory Filter GambiniPullin in
theorem solution (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun R => diskModelIntegral σ R) atTop atBot := by
  have hK : 0 < 6 * (2 + 1 / σ) ^ 2 := by positivity
  refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
  filter_upwards [eventually_ge_atTop (max 2 (5 * (6 * (2 + 1 / σ) ^ 2)))] with R hR
  have hR2 : 2 ≤ R := le_trans (le_max_left _ _) hR
  have hR5 : 5 * (6 * (2 + 1 / σ) ^ 2) ≤ R := le_trans (le_max_right _ _) hR
  have hb := gpd_disk_le σ hσ R hR2
  have h1 : 5 * R ^ 2 ≤ R ^ 3 / (6 * (2 + 1 / σ) ^ 2) := by
    rw [le_div_iff₀ hK]
    nlinarith [mul_le_mul_of_nonneg_right hR5 (sq_nonneg R)]
  show diskModelIntegral σ R ≤ -R
  nlinarith
