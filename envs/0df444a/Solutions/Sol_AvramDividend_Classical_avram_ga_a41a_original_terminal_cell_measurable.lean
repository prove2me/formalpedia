-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a41a_original_terminal_cell_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T15:43:45.080204+00:00
-- url     : https://prove2.me/submissions/e2f94534-0823-4f2a-9849-8bb693b46041

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_ga_a42_positive_only_spatial_cell_aestronglyMeasurable
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
    let Last : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      E (v (m + 1)) * (w (Z m) - w (Y (v m)))
    let F : ℕ → Ω → ℝ := fun m ω =>
      if 0 < ρ ω then max (Last m ω) (0 : ℝ) else 0
    ∀ m : ℕ, AEStronglyMeasurable (F m) P := by
  classical
  intro Last F m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → Ω → ℝ≥0 :=
    fun i ω => min ((i : ℝ≥0) * Δ) (ρ ω)
  let E : ℕ → Ω → ℝ :=
    fun i ω => Real.exp (-(q * (v i ω : ℝ)))
  let Y : ℕ → Ω → ℝ :=
    fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ :=
    fun i ω => x + X.X (v (i + 1) ω) ω - rightLimit D (v i ω) ω
  obtain ⟨hE,hY,hZ,hcell⟩ :=
    avram_ga_a43_original_clipped_spatial_cell_observations
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m
  have hwcont : ContinuousOn w (Set.Ioi (0 : ℝ)) := by
    apply hw_smooth.continuousOn.mono
    intro y hy
    exact ⟨hy, by simp [hTopCap]⟩
  have hcellm : ∀ᵐ ω ∂P,
      (E (m + 1) ω = E m ω ∧ Z m ω = Y m ω) ∨
      (0 < Y m ω ∧ 0 < Z m ω) := by
    filter_upwards [hcell] with ω hc
    exact hc m (Finset.mem_range.mpr (Nat.lt_succ_self m))
  have hSpatial : AEStronglyMeasurable
      (fun ω => E (m + 1) ω * (w (Z m ω) - w (Y m ω))) P :=
    avram_ga_a42_positive_only_spatial_cell_aestronglyMeasurable
      w hwcont (E m) (E (m + 1)) (Y m) (Z m)
      (hE m) (hE (m + 1)) (hY m) (hZ m) hcellm
  have hMax : AEStronglyMeasurable
      (fun ω => max (E (m + 1) ω *
        (w (Z m ω) - w (Y m ω))) (0 : ℝ)) P := by
    have hContinuous : Continuous (fun z : ℝ => max z 0) :=
      continuous_id.max continuous_const
    exact hContinuous.comp_aestronglyMeasurable hSpatial
  have hF : F m = (fun ω => max (E (m + 1) ω *
      (w (Z m ω) - w (Y m ω))) (0 : ℝ)) := by
    funext ω
    by_cases hρ : 0 < ρ ω
    · simp [F, Last, E, Y, Z, v, Δ, hρ]
    · have hzero : ρ ω = 0 :=
        le_antisymm (le_of_not_gt hρ) bot_le
      simp [F, Last, E, Y, Z, v, Δ, hρ, hzero]
  simpa only [hF] using hMax
