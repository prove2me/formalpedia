-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_signed_L1_to_positiveclock_mask_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:58:25.243665+00:00
-- url     : https://prove2.me/submissions/9bf007cb-a7d2-482b-98de-8f82159ef779

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_spatial_K_mask_preserves_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_masked_pospart_L1_of_signed_L1
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ρ : Ω → ℝ≥0) (hZero : MeasurableSet {ω : Ω | ρ ω = 0})
    (V U : Ω → ℝ) (Q : ℕ → Ω → ℝ) (ε : ℝ)
    (K : Ω → ℝ) (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable (fun ω => V ω - U ω - K ω - Q k ω) P)
    (hL1 : Tendsto (fun k => ∫ ω, |V ω - U ω - K ω - Q k ω| ∂P)
       Filter.atTop (nhds (0 : ℝ))) :
    ∃ K' : Ω → ℝ,
      Integrable K' P ∧ (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ ω, ρ ω = 0 → K' ω = 0) ∧
      (∀ k, Integrable (fun ω =>
        if ρ ω = 0 then (0 : ℝ)
        else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)) P) ∧
      Tendsto (fun k =>
        ∫ ω, |if ρ ω = 0 then (0 : ℝ)
          else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)| ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by
  have hs : MeasurableSet {ω : Ω | ρ ω ≠ 0} := by
    change MeasurableSet ({ω : Ω | ρ ω = 0}ᶜ)
    exact hZero.compl
  obtain ⟨K', hKI', hKsmall', hKzero, hKsame⟩ :=
    avram_pj_workerC_signed_spatial_K_mask_preserves_L1
      {ω : Ω | ρ ω ≠ 0} hs K hKI (ε / 4) hKsmall
  let Err : ℕ → Ω → ℝ := fun k ω => V ω - U ω - K ω - Q k ω
  have hErrI : ∀ k, Integrable (Err k) P := by
    intro k
    simpa only [Err] using hEI k
  have hErrL1 : Tendsto (fun k => ∫ ω, |Err k ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
    simpa only [Err] using hL1
  obtain ⟨hPosI, hPosL1⟩ :=
    avram_pj_workerF_masked_pospart_L1_of_signed_L1
      {ω : Ω | ρ ω ≠ 0} hs Err hErrI hErrL1
  have hEq (k : ℕ) :
      (fun ω => if ρ ω = 0 then (0 : ℝ)
        else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)) =
      ({ω : Ω | ρ ω ≠ 0}).indicator
        (fun ω => max (0 : ℝ) (Err k ω)) := by
    funext ω
    by_cases hz : ρ ω = 0
    · simp [Set.indicator, hz]
    · simp [Set.indicator, Err, hz, hKsame ω hz]
  refine ⟨K', hKI', hKsmall', ?_, ?_, ?_⟩
  · intro ω hz
    exact hKzero ω (by simpa using hz)
  · intro k
    rw [hEq k]
    exact hPosI k
  · have hFun :
        (fun k => ∫ ω, |if ρ ω = 0 then (0 : ℝ)
          else max (0 : ℝ) (V ω - U ω - K' ω - Q k ω)| ∂P) =
        (fun k => ∫ ω, |({ω : Ω | ρ ω ≠ 0}).indicator
          (fun ω => max (0 : ℝ) (Err k ω)) ω| ∂P) := by
        funext k
        exact integral_congr_ae (Filter.Eventually.of_forall
          (fun ω => congrArg abs (congrFun (hEq k) ω)))
    rw [hFun]
    exact hPosL1
