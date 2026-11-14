-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:46:18.149592+00:00
-- url     : https://prove2.me/submissions/b09e09b2-012c-4062-a05b-f3a4d9215520

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a215_original_prefix_raw_centered_square_cross_expected_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real physical source cross energy: prefix L1 plus source submask
measurable dominance yields full-cell integrability and L1 vanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then |R^2 - Z^2| else 0
    (∀ m : ℕ, Integrable (Cross m) P) ∧
    Tendsto (fun m : ℕ => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro Cross
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    R m i ω - (Δ m : ℝ) * X.c
  let f : ℕ → ℕ → Ω → ℝ := fun m i ω => |(R m i ω)^2 - (Z m i ω)^2|
  let A : ℕ → ℕ → Ω → Prop := fun m i ω => s m i < ρ ω
  let B : ℕ → ℕ → Ω → Prop := fun m i ω =>
    s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
  let Prefix : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m, if A m i ω then f m i ω else 0
  have hPack := avram_ga_a215_original_prefix_raw_centered_square_cross_expected_L1
    X hNuZero n ρ hρstop
  change (∀ m, Integrable (Prefix m) P) ∧
    Tendsto (fun m => ∫ ω, Prefix m ω ∂P) atTop (𝓝 (0 : ℝ)) at hPack
  have hρm : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hfMeas (m i : ℕ) : Measurable (f m i) := by
    have hXs : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le (s m i)) le_rfl
    have hXt : Measurable (X.X (s m i + Δ m)) :=
      (X.adapted (s m i + Δ m)).mono (𝓕.le (s m i + Δ m)) le_rfl
    dsimp [f,Z,R]
    fun_prop
  have hBm (m i : ℕ) : MeasurableSet {ω : Ω | B m i ω} := by
    have h1 : MeasurableSet {ω : Ω | s m i < ρ ω} :=
      (show MeasurableSet (Set.Ioi (s m i) : Set ℝ≥0)
        from measurableSet_Ioi).preimage hρm
    have h2 : MeasurableSet {ω : Ω | s m i + Δ m ≤ ρ ω} :=
      (show MeasurableSet (Set.Ici (s m i + Δ m) : Set ℝ≥0)
        from measurableSet_Ici).preimage hρm
    exact h1.inter h2
  have hTransfer := avram_ga_a213_finite_measurable_positive_mask_restriction_preserves_expected_L1_zero
    P (fun m => Finset.range m) A B f
    (fun m i ω h => h.1) (fun m i ω => abs_nonneg _)
    hfMeas hBm hPack.1 hPack.2
  change (∀ m, Integrable (Cross m) P) ∧
    Tendsto (fun m => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) at hTransfer
  exact hTransfer
