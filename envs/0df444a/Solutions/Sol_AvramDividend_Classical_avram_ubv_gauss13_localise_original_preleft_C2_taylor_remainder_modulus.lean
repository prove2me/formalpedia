-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_preleft_C2_taylor_remainder_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:09:11.440846+00:00
-- url     : https://prove2.me/submissions/f5f23f0f-3b54-4a31-8c7a-f5792dd2ece9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_hessian_modulus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (ω : Ω) (t : ℝ≥0) (y : ℝ),
          let z := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          z ∈ Set.Icc a b →
          y ∈ Set.Icc a b →
          z ≠ y →
          dist y z < δ →
          |w y - taylorWithinEval w 1 (Set.uIcc z y) z y -
            (iteratedDeriv 2 w z * (y - z) ^ 2) / 2| ≤
              ε * (y - z) ^ 2 := by
  let S : Set ℝ := {r : ℝ | 0 < r ∧ ENNReal.ofReal r < C}
  have hband : Set.Icc a b ⊆ S := by
    intro r hr
    exact ⟨lt_of_lt_of_le ha hr.1,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.2) hbcap⟩
  have hmod :=
    avram_ubv_gauss13_localise_original_preleft_hessian_modulus
      X x D hD C w hw a b ha hab hbcap
  intro ε hε
  obtain ⟨δ, hδ, hmodδ⟩ := hmod ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ω t y
  let z : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  dsimp only
  intro hz hy hne hclose
  have hsegband : Set.uIcc z y ⊆ Set.Icc a b := by
    intro r hr
    change min z y ≤ r ∧ r ≤ max z y at hr
    exact ⟨le_trans (le_min hz.1 hy.1) hr.1,
      le_trans hr.2 (max_le hz.2 hy.2)⟩
  have hseg : ContDiffOn ℝ 2 w (Set.uIcc z y) :=
    hw.mono (Set.Subset.trans hsegband hband)
  obtain ⟨ξ, hξ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hne hseg
  have hξbounds : min z y < ξ ∧ ξ < max z y := by
    simpa only [Set.uIoo, Set.mem_Ioo] using hξ
  have hξband : ξ ∈ Set.Icc a b :=
    hsegband ⟨le_of_lt hξbounds.1, le_of_lt hξbounds.2⟩
  have hdistle : dist ξ z ≤ dist y z := by
    rcases le_total z y with hzy | hyz
    · have hzξ : z ≤ ξ := by
        simpa [min_eq_left hzy] using le_of_lt hξbounds.1
      have hξy : ξ ≤ y := by
        simpa [max_eq_right hzy] using le_of_lt hξbounds.2
      rw [Real.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hzξ),
        abs_of_nonneg (sub_nonneg.mpr hzy)]
      linarith
    · have hyξ : y ≤ ξ := by
        simpa [min_eq_right hyz] using le_of_lt hξbounds.1
      have hξz : ξ ≤ z := by
        simpa [max_eq_left hyz] using le_of_lt hξbounds.2
      rw [Real.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hξz),
        abs_of_nonpos (sub_nonpos.mpr hyz)]
      linarith
  have hosc := hmodδ ω t ξ hz hξband (lt_of_le_of_lt hdistle hclose)
  have hosc' : |iteratedDeriv 2 w ξ - iteratedDeriv 2 w z| < ε := by
    simpa [iteratedDeriv_succ, iteratedDeriv_zero, Real.dist_eq] using hosc
  have hT : w y - taylorWithinEval w 1 (Set.uIcc z y) z y =
      (iteratedDeriv 2 w ξ * (y - z) ^ 2) / 2 := by
    simpa using hTaylor
  have hsq : 0 ≤ (y - z) ^ 2 := sq_nonneg _
  calc
    |w y - taylorWithinEval w 1 (Set.uIcc z y) z y -
      (iteratedDeriv 2 w z * (y - z) ^ 2) / 2| =
        |(iteratedDeriv 2 w ξ - iteratedDeriv 2 w z) *
          (y - z) ^ 2 / 2| := by rw [hT]; congr 1; ring
    _ = |iteratedDeriv 2 w ξ - iteratedDeriv 2 w z| *
      (y - z) ^ 2 / 2 := by
        rw [abs_div, abs_mul, abs_of_nonneg hsq]
        norm_num
    _ ≤ ε * (y - z) ^ 2 := by
      have hm : |iteratedDeriv 2 w ξ - iteratedDeriv 2 w z| *
          (y - z) ^ 2 ≤ ε * (y - z) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_of_lt hosc') hsq
      nlinarith