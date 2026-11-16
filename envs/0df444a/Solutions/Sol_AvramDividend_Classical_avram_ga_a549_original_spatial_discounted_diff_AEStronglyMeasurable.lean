-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a549_original_spatial_discounted_diff_AEStronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:01:47.140448+00:00
-- url     : https://prove2.me/submissions/48d85432-c523-4f37-9b4e-a5a98840d6b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun a => min ((a : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun a =>
        x + X.X (v (a + 1)) ω - rightLimit D (v a) ω
      if 0 < ρ ω then E (v (i + 1)) * (w (Z i) - w (Y (v i))) else 0
    ∀ m i : ℕ, i < m →
      AEStronglyMeasurable (A m i) P := by
  classical
  intro A m i hi
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 := fun k ω => min ((k : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ := fun k ω => Real.exp (-(q * (v k ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun k ω =>
    x + X.X (v k ω) ω - rightLimit D (v k ω) ω
  let Z : ℕ → Ω → ℝ := fun k ω =>
    x + X.X (v (k + 1) ω) ω - rightLimit D (v k ω) ω
  obtain ⟨hE, hY, hZ, hAlt⟩ :=
    avram_ga_a43_original_clipped_spatial_cell_observations
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  have hDiff : ContinuousOn w (Set.Ioi (0 : ℝ)) := by
    apply hw_smooth.continuousOn.mono
    intro y hy
    simpa [hTopCap, Set.mem_Ioi] using hy
  have hCellAlt : ∀ᵐ ω ∂P, Y i ω = Z i ω ∨
      (0 < Y i ω ∧ 0 < Z i ω) := by
    filter_upwards [hAlt] with ω hw
    rcases hw i (Finset.mem_range.mpr (by omega : i < m + 1)) with h | h
    · exact Or.inl h.2.symm
    · exact Or.inr h
  have hCore := avram_ga_a535_active_positive_domain_spatial_cell_aemeasurable
    P w hDiff (Y i) (Z i) (E (i + 1))
    (hY i) (hZ i) (hE (i + 1)) hCellAlt
  have hρm : Measurable (fun ω : Ω => (ρ ω : WithTop ℝ≥0)) :=
    hρstop.measurable.mono hρstop.measurableSpace_le le_rfl
  have hEvent : MeasurableSet {ω : Ω | 0 < ρ ω} := by
    have ht : MeasurableSet
        {ω : Ω | (0 : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ioi.preimage hρm
    convert ht using 1
    ext ω
    change (0 : ℝ≥0) < ρ ω ↔
      (((0 : ℝ≥0) : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0))
    exact (WithTop.coe_lt_coe).symm
  have hSource : A m i =
      Set.indicator {ω : Ω | 0 < ρ ω}
        (fun ω => E (i + 1) ω * (w (Z i ω) - w (Y i ω))) := by
    funext ω
    simp [A, Δ, v, E, Y, Z, Set.indicator]
  rw [hSource]
  exact (hCore.aemeasurable.indicator hEvent).aestronglyMeasurable
