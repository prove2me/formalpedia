-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite50_zerojump_cap_strip_gradient_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:44:22.563126+00:00
-- url     : https://prove2.me/submissions/8090b5c9-ce45-42ce-a7b5-824301858071

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_zerojump_hjb_exponential_spatial_control
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (a c : ℝ) (hac : a < c)
    (hNonneg : ∀ y ∈ Ico a c, 0 ≤ w y)
    (hGrad : ∀ y ∈ Ico a c, 0 ≤ deriv w y)
    (hHJB : ∀ y ∈ Ico a c, X.generator w y - q * w y ≤ 0)
    (hDer1 : ∀ y ∈ Ico a c, HasDerivAt w (deriv w y) y)
    (hDer2 : ∀ y ∈ Ico a c,
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Ico a c, deriv w y ≤ B := by
  let K : ℝ := 1 + 2 * (q + |X.c|) / X.σ ^ 2
  let B : ℝ := Real.exp (K * (c - a)) * (w a + deriv w a)
  have ha : a ∈ Ico a c := ⟨le_rfl, hac⟩
  have hP : 0 ≤ w a + deriv w a :=
    add_nonneg (hNonneg a ha) (hGrad a ha)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hNum : 0 ≤ 2 * (q + |X.c|) :=
      mul_nonneg (by norm_num) (add_nonneg hq (abs_nonneg _))
    have hDen : 0 ≤ X.σ ^ 2 := sq_nonneg _
    have hDiv := div_nonneg hNum hDen
    linarith
  have hB : 0 ≤ B := by
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) hP
  refine ⟨B, hB, ?_⟩
  intro y hy
  have hSub : Icc a y ⊆ Ico a c := by
    intro z hz
    exact ⟨hz.1, lt_of_le_of_lt hz.2 hy.2⟩
  have hComp : w y + deriv w y ≤
      Real.exp (K * (y - a)) * (w a + deriv w a) := by
    simpa only [K] using
      (avram_gsource15_zerojump_hjb_exponential_spatial_control
        X hν hσ q hq w a y hy.1
        (fun z hz => hNonneg z (hSub hz))
        (fun z hz => hGrad z (hSub hz))
        (fun z hz => hHJB z (hSub hz))
        (fun z hz => hDer1 z (hSub hz))
        (fun z hz => hDer2 z (hSub hz)))
  have hExp : Real.exp (K * (y - a)) ≤
      Real.exp (K * (c - a)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (le_of_lt hy.2) a) hK
  have hBound : w y + deriv w y ≤ B := by
    exact le_trans hComp (mul_le_mul_of_nonneg_right hExp hP)
  have hLower : deriv w y ≤ w y + deriv w y := by
    linarith [hNonneg y hy]
  exact le_trans hLower hBound
