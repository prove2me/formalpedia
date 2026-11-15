-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a342_original_small_fullcell_combined_positive_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:33:14.152743+00:00
-- url     : https://prove2.me/submissions/1a8f2c0f-3b2b-4035-aa62-d0d210d707d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a322_finite_masked_combined_Gaussian_raw_centered_C2_source_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a163_original_full_mesh_source_endpoint_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1))
    (δ : ℝ) (hδ : 0 < δ) :
    let Small : ℝ → ℕ → Ω → ℝ := fun δ m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * R i +
        (iteratedDeriv 2 w (Y (s i)) / 2) * Z i^2)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω ∧ |R i| < δ then F i else 0
    ∀ δ : ℝ, 0 < δ → ∀ m,
      AEStronglyMeasurable (fun ω => max (Small δ m ω) 0) P := by
  intro Small δ hδ m
  let Δ : ℝ≥0 := (n : ℝ≥0)/((m : ℝ≥0)+1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0)*Δ
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q*(t : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω => x+X.X (s i) ω-rightLimit D (s i) ω
  let R : ℕ → Ω → ℝ := fun i ω => X.X (s i+Δ) ω-X.X (s i) ω
  let A : ℕ → Ω → Prop := fun i ω =>
    (s i < ρ ω ∧ s i+Δ ≤ ρ ω) ∧ |R i ω| < δ
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hopen.uniqueDiffOn
  have hSub : Ioi (0 : ℝ) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy; exact ⟨hy, by simp [hTopCap]⟩
  have h0 : ContinuousOn w (Ioi (0 : ℝ)) := hw_smooth.continuousOn.mono hSub
  have h1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)) := by
    have hc := hw_smooth.continuousOn_iteratedDerivWithin
      (by norm_num : (1 : WithTop ENat) ≤ (2 : WithTop ENat)) hu
    have heq := iteratedDerivWithin_of_isOpen hopen (n := 1) (f := w)
    simpa only [iteratedDeriv_one] using (hc.congr heq.symm).mono hSub
  have h2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)) := by
    have hc := hw_smooth.continuousOn_iteratedDerivWithin
      (by norm_num : (2 : WithTop ENat) ≤ (2 : WithTop ENat)) hu
    exact (hc.congr
      (iteratedDerivWithin_of_isOpen hopen (n := 2) (f := w)).symm).mono hSub
  have hρm : Measurable ρ := measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hY (i : ℕ) : Measurable (Y i) := by
    exact (measurable_const.add ((X.adapted (s i)).mono (𝓕.le _) le_rfl)).sub
      (dividendStrategy_rightLimit_measurable D hD.1.1 (s i))
  have hR (i : ℕ) : Measurable (R i) := by
    exact ((X.adapted (s i+Δ)).mono (𝓕.le _) le_rfl).sub
      ((X.adapted (s i)).mono (𝓕.le _) le_rfl)
  have hA (i : ℕ) : MeasurableSet {ω : Ω | A i ω} := by
    have ha : MeasurableSet {ω : Ω | s i < ρ ω} :=
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (s i))).preimage hρm
    have hb : MeasurableSet {ω : Ω | s i+Δ ≤ ρ ω} :=
      (measurableSet_Ici : MeasurableSet (Set.Ici (s i+Δ))).preimage hρm
    have hc : MeasurableSet {ω : Ω | |R i ω| < δ} :=
      (measurableSet_Iio : MeasurableSet (Set.Iio δ)).preimage (hR i).abs
    exact (ha.inter hb).inter hc
  have hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω ∧ 0 < Y i ω+R i ω := by
    filter_upwards [avram_ga_a163_original_full_mesh_source_endpoint_positive
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m] with ω hw
    intro i hi ha; exact hw i hi ha.1
  have hMeasured :=
    avram_ga_a322_finite_masked_combined_Gaussian_raw_centered_C2_source_aestrongly_measurable
      P w h0 h1 h2 m A hA Y R hY hR hPos
      (Δ : ℝ) X.c X.σ (fun i => E (s i)) (fun i => E (s i+Δ))
  have hc : Continuous (fun z : ℝ => max z 0) := continuous_id.max continuous_const
  have hM : AEStronglyMeasurable (Small δ m) P :=
    hMeasured.congr (Filter.Eventually.of_forall (fun ω => by
      simp only [Small, A, E, Y, R, s, Δ, and_assoc]))
  simpa only [Function.comp_apply] using hc.comp_aestronglyMeasurable hM
