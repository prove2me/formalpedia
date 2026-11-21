-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_masked_pospart_L1_of_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:51:54.104494+00:00
-- url     : https://prove2.me/submissions/3268498a-dc7a-4126-bef4-8b4f41e9c258

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S)
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ k, Integrable (E k) P)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (nhds (0 : ℝ))) :
    (∀ k, Integrable (S.indicator (fun ω => max (0 : ℝ) (E k ω))) P) ∧
    Tendsto (fun k => ∫ ω, |S.indicator
      (fun ω => max (0 : ℝ) (E k ω)) ω| ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by
  let Pos : ℕ → Ω → ℝ := fun k =>
    S.indicator (fun ω => max (0 : ℝ) (E k ω))
  have hPI : ∀ k, Integrable (Pos k) P := by
    intro k
    exact ((integrable_zero Ω ℝ P).sup (hEI k)).indicator hS
  have hBound : ∀ k ω, |Pos k ω| ≤ |E k ω| := by
    intro k ω
    by_cases hs : ω ∈ S
    · rw [show Pos k ω = max (0 : ℝ) (E k ω) by
        simp [Pos, Set.indicator_of_mem hs]]
      rw [abs_of_nonneg (le_max_left (0 : ℝ) (E k ω))]
      exact max_le (abs_nonneg _) (le_abs_self _)
    · rw [show Pos k ω = 0 by
        simp [Pos, Set.indicator_of_notMem hs]]
      simpa using (abs_nonneg (E k ω))
  have hLower : ∀ k, 0 ≤ (∫ ω, |Pos k ω| ∂P) :=
    fun k => integral_nonneg (fun ω => abs_nonneg _)
  have hUpper : ∀ k,
      (∫ ω, |Pos k ω| ∂P) ≤ (∫ ω, |E k ω| ∂P) :=
    fun k => integral_mono_ae (hPI k).abs (hEI k).abs
      (Filter.Eventually.of_forall (hBound k))
  have hPL1 : Tendsto (fun k => ∫ ω, |Pos k ω| ∂P)
      atTop (nhds (0 : ℝ)) :=
    squeeze_zero hLower hUpper hVan
  exact ⟨hPI, hPL1⟩
