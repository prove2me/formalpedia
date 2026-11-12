-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger160_original_clipped_discount_euler_grid_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:48:25.538897+00:00
-- url     : https://prove2.me/submissions/7bfa1368-d511-4d5d-abd0-f07009ae0907

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger174_clipped_discount_compact_weight_replacement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω,
      τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
    ∀ m : ℕ, AEStronglyMeasurable (A m) P := by
  intro A m; classical
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let a : ℝ := 1 / ((j : ℝ) + 1); let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hSub : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy; exact ⟨lt_of_lt_of_le ha hy.1, by simp [hTopCap]⟩
  have h0 : ContinuousOn w (Icc a b) := hw_smooth.continuousOn.mono hSub
  let H : ℝ → ℝ := fun y => if y ∈ Icc a b then w y else 0
  have hHm : Measurable H :=
    h0.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  have hρm : Measurable ρ := by
    have ht := (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
    convert (ht.untopD (0 : ℝ≥0)) using 1
    funext ω; rfl
  have hv (i : ℕ) : Measurable (fun ω => min ((i : ℝ≥0) * Δ) (ρ ω)) :=
    measurable_const.min hρm
  have he (i : ℕ) : Measurable (fun ω =>
      Real.exp (-(q * ((min ((i : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : ℝ)))) := by
    have hm := hv i; fun_prop
  have hy (i : ℕ) : Measurable (fun ω =>
      x + X.X (min ((i : ℝ≥0) * Δ) (ρ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω) := by
    obtain ⟨hXmi, hDmi⟩ :=
      avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
        X hX D hD.1.1 ρ hρstop Δ i
    exact (measurable_const.add hXmi).sub hDmi
  let F : Ω → ℝ := fun ω =>
    (∑ i ∈ Finset.range (m + 1),
      (Real.exp (-(q * ((min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : ℝ))) -
       Real.exp (-(q * ((min ((i : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : ℝ)))) *
       H (x + X.X (min ((i : ℝ≥0) * Δ) (ρ ω)) ω -
          rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω)) +
     ∑ i ∈ Finset.range m,
       let s : ℝ≥0 := (i : ℝ≥0) * Δ
       if s < ρ ω then q * (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
          H (x + X.X s ω - rightLimit D s ω) else 0
  have hFm : Measurable F := by
    apply Measurable.add
    · apply Finset.measurable_sum
      intro i hi; exact ((he (i + 1)).sub (he i)).mul (hHm.comp (hy i))
    · apply Finset.measurable_sum
      intro i hi
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      have hXm : Measurable (X.X s) := (X.adapted s).mono (𝓕.le s) le_rfl
      have hDm : Measurable (fun ω => rightLimit D s ω) :=
        dividendStrategy_rightLimit_measurable D hD.1.1 s
      have hsm : MeasurableSet {ω : Ω | s < ρ ω} := (measurableSet_Ioi : MeasurableSet (Ioi s)).preimage hρm
      exact Measurable.ite hsm
        (measurable_const.mul (hHm.comp ((measurable_const.add hXm).sub hDm))) measurable_const
  have hband : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω → x + X.X t ω - rightLimit D t ω ∈ Icc a b := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band X x D hD.1.1 ρ j hprefix
  have hFEq : ∀ᵐ ω ∂P, F ω = A m ω := by
    filter_upwards [hband] with ω hω
    have hHw : ∀ t : ℝ≥0, t < ρ ω →
        H (x + X.X t ω - rightLimit D t ω) =
          w (x + X.X t ω - rightLimit D t ω) := by
      intro t ht
      simp only [H, if_pos (hω t ht)]
    exact avram_gledger174_clipped_discount_compact_weight_replacement
      n m (ρ ω) q w H (fun t => x + X.X t ω - rightLimit D t ω) hHw
  exact hFm.aestronglyMeasurable.congr hFEq
