-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a277_original_gaussian_true_physical_signed_rare_exponential_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:26:11.368025+00:00
-- url     : https://prove2.me/submissions/21e0934e-9b77-40d0-b9c9-c6a7f8e7f396

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (theta delta : ℝ) (hθ : 0 ≤ theta) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0)+1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0)*Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i+Δ m) ω-X.X (s m i) ω
    let Signed : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
        then Real.exp (theta*R m i ω) else 0
    ∀ m, Integrable (Signed m) P := by
  classical
  intro Δ s R Signed m
  have hρm : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  change Integrable (fun ω => ∑ i ∈ Finset.range m,
    if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
    then Real.exp (theta*R m i ω) else 0) P
  apply integrable_finset_sum
  intro i hi
  have hR : Measurable (R m i) := by
    exact ((X.adapted (s m i+Δ m)).mono (𝓕.le _) le_rfl).sub
      ((X.adapted (s m i)).mono (𝓕.le _) le_rfl)
  have hStart : MeasurableSet {ω : Ω | s m i < ρ ω} :=
    (show MeasurableSet (Set.Ioi (s m i) : Set ℝ≥0)
      from measurableSet_Ioi).preimage hρm
  have hEnd : MeasurableSet {ω : Ω | s m i+Δ m ≤ ρ ω} :=
    (show MeasurableSet (Set.Ici (s m i+Δ m) : Set ℝ≥0)
      from measurableSet_Ici).preimage hρm
  have hRare : MeasurableSet {ω : Ω | delta ≤ |R m i ω|} :=
    (show MeasurableSet (Set.Ici delta : Set ℝ)
      from measurableSet_Ici).preimage hR.norm
  have hMask : MeasurableSet
      {ω : Ω | (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|} :=
    (hStart.inter hEnd).inter hRare
  have hst : s m i ≤ s m i+Δ m :=
    le_add_of_nonneg_right (by positivity)
  have he := avram_ga_a276_original_zerojump_Gaussian_raw_increment_exponential_integrable
    X hν hσ (s m i) (s m i+Δ m) hst theta hθ
  have hi := he.indicator hMask
  have hEq : (fun ω : Ω =>
      if (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
      then Real.exp (theta*R m i ω) else 0) =
      Set.indicator
        {ω : Ω | (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|}
        (fun ω => Real.exp (theta*R m i ω)) := by
    funext ω
    by_cases h : (s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω) ∧ delta ≤ |R m i ω|
    <;> simp [Set.indicator,h]
  rw [hEq]
  simpa only [R] using hi
