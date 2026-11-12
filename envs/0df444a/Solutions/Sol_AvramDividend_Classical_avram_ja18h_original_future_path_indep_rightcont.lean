-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18h_original_future_path_indep_rightcont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:52:05.372737+00:00
-- url     : https://prove2.me/submissions/930c63b9-ad12-4139-a91a-1dfa658575cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A deterministic stopping clock turns original stopped-source strong Markov
independence into independence from the right-continuous time-s past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) :
    ProbabilityTheory.Indep (𝓕.rightCont s)
      (MeasurableSpace.comap (fun ω : Ω => fun u : ℝ≥0 =>
        X.X (s + u) ω - X.X s ω) inferInstance) P := by
  classical
  let τ : Ω → ℝ≥0 := fun _ => s
  have hτ : ∀ r : ℝ≥0,
      MeasurableSet[𝓕.rightCont r] {ω : Ω | τ ω ≤ r} := by
    intro r
    by_cases h : s ≤ r
    · have heq : {ω : Ω | τ ω ≤ r} = Set.univ := by ext ω; simp [τ, h]
      rw [heq]
      exact (MeasurableSet.univ : MeasurableSet[𝓕.rightCont r] (Set.univ : Set Ω))
    · have heq : {ω : Ω | τ ω ≤ r} = ∅ := by ext ω; simp [τ, h]
      rw [heq]
      exact (@MeasurableSet.empty Ω (𝓕.rightCont r))
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  have hPastLe : 𝓕.rightCont s ≤ hstop.measurableSpace := by
    intro A hA
    apply (hstop.measurableSet A).2
    constructor
    · exact (le_iSup (fun r => 𝓕.rightCont r) s) A hA
    · intro r
      by_cases h : s ≤ r
      · have hAr : MeasurableSet[𝓕.rightCont r] A :=
          ((𝓕.rightCont).mono h) A hA
        have hcoe : (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0) := by
          exact_mod_cast h
        have heq : (A ∩ {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) = A := by
          ext ω
          change (ω ∈ A ∧ (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)) ↔ ω ∈ A
          constructor
          · exact And.left
          · intro hmem
            exact ⟨hmem, hcoe⟩
        rw [heq]
        exact hAr
      · have hcoe : ¬ ((s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)) := by
          simpa only [WithTop.coe_le_coe] using h
        have heq : (A ∩ {ω : Ω | (τ ω : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)}) = ∅ := by
          ext ω
          change (ω ∈ A ∧ (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)) ↔ False
          constructor
          · intro hmem
            exact hcoe hmem.2
          · intro hFalse
            exact hFalse.elim
        rw [heq]
        exact (@MeasurableSet.empty Ω (𝓕.rightCont r))
  have hShift := avram_wave5_03a_actual_rightCont_stoppedSigma_indep_shifted_source
    X τ hτ
  have hInd := indep_of_indep_of_le_left hShift hPastLe
  simpa only [τ] using hInd
