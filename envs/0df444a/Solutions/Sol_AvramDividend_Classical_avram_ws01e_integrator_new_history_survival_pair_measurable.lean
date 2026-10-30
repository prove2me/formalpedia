-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_history_survival_pair_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:43:36.226681+00:00
-- url     : https://prove2.me/submissions/87418b09-6cab-41ef-9c3b-dea0fdfe2da0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal
attribute [local instance] Classical.propDecidable

/-- The actual current Lévy endpoint and the entire closed-past survival flag
form one measurable historical state for deterministic Markov–Tonelli. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (s : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) :
    Measurable[𝓕 s]
      (fun ω : Ω => (X.X s ω,
        decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω))) := by
  classical
  let B : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let C : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → ¬ X.X v ω < -x}
  have hEq : B = C := by
    ext ω
    constructor
    · intro h v hv
      have h0 : 0 ≤ x + X.X v ω := h v hv
      exact not_lt.mpr (by linarith)
    · intro h v hv
      have h0 : -x ≤ X.X v ω := not_lt.mp (h v hv)
      linarith
  have hC : MeasurableSet[𝓕 s] C :=
    chat03_lower_survival_filtration_measurable X τ hCover (-x) s
  have hB : MeasurableSet[𝓕 s] B := by
    rw [hEq]
    exact hC
  have hIte : Measurable[𝓕 s]
      (fun ω : Ω => if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω
        then true else false) :=
    Measurable.ite hB measurable_const measurable_const
  have hDec : Measurable[𝓕 s]
      (fun ω : Ω => decide (∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω)) := by
    convert hIte using 1
    funext ω
    by_cases hp : ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω
    · simp [hp]
    · simp [hp]
  exact (X.adapted s).prodMk hDec
