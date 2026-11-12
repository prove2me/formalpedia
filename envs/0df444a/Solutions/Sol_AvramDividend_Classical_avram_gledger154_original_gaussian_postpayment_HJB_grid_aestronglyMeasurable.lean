-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger154_original_gaussian_postpayment_HJB_grid_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:58:13.489198+00:00
-- url     : https://prove2.me/submissions/dad3eb1c-f644-4e76-b8a9-b89f7c265902

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation)
    (hSigmaNonzero : X.σ ≠ 0) (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let G : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1); Finset.sum (Finset.range m) (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          let y := x + X.X s ω - rightLimit D s ω
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * (X.generator w y - q * w y)
        else 0)
    ∀ m : ℕ, AEStronglyMeasurable (G m) P := by
  intro G m
  let a : ℝ := 1 / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hSub : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy; exact ⟨lt_of_lt_of_le ha hy.1, by simp [hTopCap]⟩
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := hopen.uniqueDiffOn
  have h0 : ContinuousOn w (Icc a b) := hw_smooth.continuousOn.mono hSub
  have h1 : ContinuousOn (deriv w) (Icc a b) := by
    have hc : ContinuousOn
        (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      hw_smooth.continuousOn_iteratedDerivWithin (by norm_num) hu
    have heq := iteratedDerivWithin_of_isOpen hopen (n := 1) (f := w)
    simpa only [iteratedDeriv_one] using (hc.congr heq.symm).mono hSub
  have h2 : ContinuousOn (iteratedDeriv 2 w) (Icc a b) := by
    have hc : ContinuousOn
        (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
      hw_smooth.continuousOn_iteratedDerivWithin (by norm_num) hu
    have heq := iteratedDerivWithin_of_isOpen hopen (n := 2) (f := w)
    exact (hc.congr heq.symm).mono hSub
  let V : ℝ → ℝ := fun y => X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y - q * w y
  have hV : ContinuousOn V (Icc a b) := ((continuousOn_const.mul h2).add (continuousOn_const.mul h1)).sub (continuousOn_const.mul h0)
  let H : ℝ → ℝ := fun y => if y ∈ Icc a b then V y else 0
  have hHm : Measurable H := hV.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  have hρm : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) := (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hband : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b := by
    filter_upwards [avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD.1.1 ρ j hprefix] with ω hω
    intro t ht; exact hω t ht
  let F : Ω → ℝ := fun ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    Finset.sum (Finset.range m) (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω then (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) * H
        (x + X.X s ω - rightLimit D s ω) else 0)
  have hFm : Measurable F := by
    classical
    dsimp [F]
    apply Finset.measurable_sum
    intro i hi
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    have hXm : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
    have hDm : Measurable (fun ω => rightLimit D s ω) := dividendStrategy_rightLimit_measurable D hD.1.1 s
    have hYm : Measurable (fun ω => x + X.X s ω - rightLimit D s ω) := (measurable_const.add hXm).sub hDm
    have hsm : MeasurableSet {ω : Ω | s < ρ ω} := by
      have hm : MeasurableSet {ω : Ω |
          (s : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0)} := measurableSet_Ioi.preimage hρm
      simpa only [WithTop.coe_lt_coe] using hm
    exact Measurable.ite hsm
      (measurable_const.mul (hHm.comp hYm)) measurable_const
  have hFEq : ∀ᵐ ω ∂P, F ω = G m ω := by
    filter_upwards [hband] with ω hω
    dsimp [F, G]
    apply Finset.sum_congr rfl
    intro i hi
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    change
      (if s < ρ ω then (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
        H (x + X.X s ω - rightLimit D s ω) else 0) =
      (if s < ρ ω then (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
        (X.generator w (x + X.X s ω - rightLimit D s ω) -
          q * w (x + X.X s ω - rightLimit D s ω)) else 0)
    by_cases hs : s < ρ ω
    · have hy := hω s hs
      simp only [if_pos hs, H, if_pos hy, V]
      rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hNuZero w
        (x + X.X s ω - rightLimit D s ω)]
    · simp only [if_neg hs]
  exact hFm.aestronglyMeasurable.congr hFEq
