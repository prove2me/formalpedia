-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin20_original_true_spatial_clocks_with_cofinality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T09:07:07.110215+00:00
-- url     : https://prove2.me/submissions/06d12dcb-0d58-488e-9c43-0f9547458c13

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_upper_exit_spatial_cofinality
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℝ≥0)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ (S : ℕ → Ω → ℝ≥0∞) (L : ℕ → Ω → ℝ≥0),
      (∀ k ω, S k ω = twoSidedExitUpTime X ((k : ℝ) + 1) ω) ∧
      (∀ ω, Monotone (fun k => S k ω)) ∧
      (∀ ω, (⨆ k : ℕ, S k ω) = ⊤) ∧
      (∀ k ω, L k ω = (min (ρ ω : ℝ≥0∞) (S k ω)).toNNReal) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (L k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, L k ω ≤ ρ ω) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, L k ω = ρ ω) := by
  classical
  let S : ℕ → Ω → ℝ≥0∞ := fun k ω => twoSidedExitUpTime X ((k : ℝ) + 1) ω
  let L : ℕ → Ω → ℝ≥0 :=
    fun k ω => (min (ρ ω : ℝ≥0∞) (S k ω)).toNNReal
  have hCoe (k : ℕ) (ω : Ω) :
      (L k ω : ℝ≥0∞) = min (ρ ω : ℝ≥0∞) (S k ω) := by
    have hle : min (ρ ω : ℝ≥0∞) (S k ω) ≤ (ρ ω : ℝ≥0∞) :=
      min_le_left _ _
    have hf : min (ρ ω : ℝ≥0∞) (S k ω) ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp) hle
    exact ENNReal.coe_toNNReal hf
  have hSstop (k : ℕ) : IsStoppingTime 𝓕.rightCont (S k) :=
    upperPassage_stopping_rightCont_filtration X ((k : ℝ) + 1)
  have hStop (k : ℕ) :
      IsStoppingTime 𝓕.rightCont
        (fun ω => (L k ω : WithTop ℝ≥0)) := by
    have hMin : IsStoppingTime 𝓕.rightCont
        (fun ω => min (ρ ω : WithTop ℝ≥0) (S k ω)) := by
      intro t
      have heq : {ω : Ω | min (ρ ω : WithTop ℝ≥0) (S k ω) ≤ t} =
          {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ t} ∪
          {ω : Ω | S k ω ≤ t} := by
        ext ω
        exact (min_le_iff : min (ρ ω : WithTop ℝ≥0) (S k ω) ≤ t ↔
          (ρ ω : WithTop ℝ≥0) ≤ t ∨ S k ω ≤ t)
      rw [heq]
      exact (hρstop t).union (hSstop k t)
    have heq : (fun ω => (L k ω : WithTop ℝ≥0)) =
        (fun ω => min (ρ ω : WithTop ℝ≥0) (S k ω)) := by
      funext ω
      exact hCoe k ω
    rw [heq]
    exact hMin
  have hLe (k : ℕ) (ω : Ω) : L k ω ≤ ρ ω := by
    apply ENNReal.coe_le_coe.mp
    rw [hCoe]
    exact min_le_left _ _
  have hEventually (ω : Ω) :
      ∀ᶠ k : ℕ in atTop, L k ω = ρ ω := by
    obtain ⟨N, hN⟩ :=
      firstUpcrossing_record_grid_clocks_eventually_ge_horizon
        X ω n 1 1 (by norm_num)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hSge : (n : ℝ≥0∞) ≤ S k ω := by
      simpa [S, twoSidedExitUpTime, mul_one, add_comm] using hN k hk
    apply ENNReal.coe_injective
    rw [hCoe]
    exact min_eq_left (le_trans (ENNReal.coe_le_coe.mpr (hρle ω)) hSge)
  refine ⟨S, L, (by intro k ω; rfl), ?_, ?_, (by intro k ω; rfl),
    hStop, hLe, hEventually⟩
  · intro ω
    exact (avram_mix_fin20_original_true_upper_exit_spatial_cofinality X ω).1
  · intro ω
    exact (avram_mix_fin20_original_true_upper_exit_spatial_cofinality X ω).2
