-- Prove2me | solution 2 for AvramDividend.Classical.levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:17:46.430999+00:00
-- url     : https://prove2.me/submissions/2f0eceab-1af1-4d51-bc36-17f8db9b0918

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hAtom : ∀ (t : ℝ≥0), 0 < t →
      P {ω : Ω |
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} = 0} = 0) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ≥0), 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by
  let δ : ℕ → ℝ≥0 := fun n =>
    ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hδpos (n : ℕ) : 0 < δ n := by
    apply NNReal.coe_pos.mp
    change (0 : ℝ) < 1 / ((n : ℝ) + 1)
    positivity
  have hδreal : Tendsto (fun n : ℕ => (δ n : ℝ))
      atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0)
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hδ : Tendsto δ atTop (𝓝 (0 : ℝ≥0)) :=
    (NNReal.tendsto_coe).mp hδreal
  have hEach (n : ℕ) :
      ∀ᵐ ω ∂P,
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ δ n ∧ y = X.X s ω} ≠ 0 := by
    have hzero := hAtom (δ n) (hδpos n)
    exact measure_eq_zero_iff_ae_notMem.mp hzero
  have hAll :
      ∀ᵐ ω ∂P, ∀ n : ℕ,
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ δ n ∧ y = X.X s ω} ≠ 0 :=
    ae_all_iff.mpr hEach
  filter_upwards [hAll] with ω hω
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, δ n < ε :=
    hδ.eventually (Iio_mem_nhds hε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  have hδlt : δ N < ε := hN N le_rfl
  have hNot : ¬ ∀ s : ℝ≥0, s ≤ δ N → 0 ≤ X.X s ω := by
    intro hsurv
    have hle :
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ δ N ∧ y = X.X s ω} ≤ 0 := by
      apply (chat04_reflected_infimum_Iic_iff_survival X (δ N) ω 0).mpr
      simpa using hsurv
    exact (hω N) (le_antisymm hle
      (chat04_negative_running_infimum_nonneg X (δ N) ω))
  push_neg at hNot
  obtain ⟨s, hs, hneg⟩ := hNot
  exact ⟨s, lt_of_le_of_lt hs hδlt, hneg⟩
