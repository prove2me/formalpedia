-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:03:39.951762+00:00
-- url     : https://prove2.me/submissions/ffc1a3a3-79c1-4e5c-8f98-05b18530848b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped physical raw large-square tail is real-integrable
because centred Gaussian squares and raw-centred cross squares are. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) :
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then (if η ≤ |r| then r^2 else 0) else 0
    ∀ m, Integrable (Tail m) P := by
  classical
  intro Tail m
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X (s m i + Δ m) ω - X.X (s m i) ω - (Δ m : ℝ) * X.c
  let E : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω then (Z m i ω)^2 else 0
  let A : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ Finset.range m,
      if s m i < ρ ω then
        |(Z m i ω + (Δ m : ℝ) * X.c)^2 - (Z m i ω)^2| else 0
  have hPack := avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
    X hν n ρ hρstop
  change (∀ m, Integrable (A m) P) ∧
    (∀ m, Integrable (E m) P) ∧
    (∀ m, (∫ ω, E m ω ∂P) ≤ (n : ℝ) * X.σ^2) at hPack
  have hρm : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hMask (i : ℕ) :
      MeasurableSet {ω : Ω | s m i < ρ ω} := by
    have hh : MeasurableSet {ω : Ω |
        (s m i : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ioi.preimage hρm
    simpa only [WithTop.coe_lt_coe] using hh
  have hZm (i : ℕ) : Measurable (Z m i) := by
    have h1 : Measurable (X.X (s m i + Δ m)) :=
      (X.adapted (s m i + Δ m)).mono (𝓕.le _) le_rfl
    have h0 : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le _) le_rfl
    exact (h1.sub h0).sub measurable_const
  have hRawI := avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
    P (Finset.range m) (fun i ω => s m i < ρ ω)
      hMask (Z m) hZm ((Δ m : ℝ) * X.c) η
      (hPack.2.1 m) (hPack.1 m)
  have hEq (ω : Ω) :
      Tail m ω = ∑ i ∈ Finset.range m,
        if s m i < ρ ω then
          (if η ≤ |Z m i ω + (Δ m : ℝ) * X.c| then
            (Z m i ω + (Δ m : ℝ) * X.c)^2 else 0) else 0 := by
    dsimp [Tail, Z, s, Δ]
    simp only [sub_add_cancel]
  exact hRawI.congr (Filter.Eventually.of_forall (fun ω => (hEq ω).symm))
