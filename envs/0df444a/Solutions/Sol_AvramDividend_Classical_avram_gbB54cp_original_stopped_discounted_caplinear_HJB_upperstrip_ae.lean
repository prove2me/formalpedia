-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54cp_original_stopped_discounted_caplinear_HJB_upperstrip_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:35:09.155933+00:00
-- url     : https://prove2.me/submissions/0cc91e5b-12ae-44ca-aa97-54f978d2d96b

import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_original_stopped_true_caplinear_generator_pointwise_upperstrip_ae
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (b : ℝ)
    (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let μ : Measure ℝ := volume.restrict S
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
      ∀ᵐ t ∂μ,
        Real.exp (-(q * t)) *
          (X.generator V (Y t) - q * V (Y t)) ≤
          if b < Y t then max X.c 0 else 0 := by
  classical
  have hEnv :=
    avram_gbB54cp_original_stopped_true_caplinear_generator_pointwise_upperstrip_ae
      X hBV hν q hq w b hwb hHJB x D hD n ρ δ hδ hFloor
  filter_upwards [hEnv] with ω hω
  intro S μ Y V
  have hS : MeasurableSet S := by
    change MeasurableSet {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
    exact (measurableSet_lt measurable_const measurable_id).inter
      ((measurableSet_lt measurable_id measurable_const).inter
        (measurableSet_lt measurable_id measurable_const))
  have hTime : ∀ᵐ t ∂μ, 0 ≤ t := by
    filter_upwards [ae_restrict_mem hS] with t ht
    exact le_of_lt ht.1
  filter_upwards [hω, hTime] with t hP ht
  have hE0 : 0 ≤ Real.exp (-(q * t)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(q * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg hq ht)
  have hU : 0 ≤ (if b < Y t then max X.c 0 else (0 : ℝ)) := by
    split_ifs <;> simp
  calc
    Real.exp (-(q * t)) *
        (X.generator V (Y t) - q * V (Y t)) ≤
        Real.exp (-(q * t)) * (if b < Y t then max X.c 0 else (0 : ℝ)) :=
      mul_le_mul_of_nonneg_left hP hE0
    _ ≤ (1 : ℝ) * (if b < Y t then max X.c 0 else (0 : ℝ)) :=
      mul_le_mul_of_nonneg_right hE1 hU
    _ = _ := one_mul _
