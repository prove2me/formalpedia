-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_signed_one_sided_L1_source_to_nonnegative_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T22:36:07.074148+00:00
-- url     : https://prove2.me/submissions/ce7d1a66-8691-4d64-8a65-a4e9ec55d773

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V U K : Ω → ℝ) (E : ℕ → Ω → ℝ)
    (S : Set Ω) (ε : ℝ)
    (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable (E k) P)
    (hUpper : ∀ k, ∀ᵐ ω ∂P,
      ω ∈ S → V ω - U ω ≤ K ω + E k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (nhds (0 : ℝ))) :
    ∃ K' : Ω → ℝ, ∃ E' : ℕ → Ω → ℝ,
      Integrable K' P ∧
      (∫ ω, |K' ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E' k) P) ∧
      (∀ᵐ ω ∂P, 0 ≤ K' ω) ∧
      (∀ k, ∀ᵐ ω ∂P, 0 ≤ E' k ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ω ∈ S →
        V ω - U ω ≤ K' ω + E' k ω) ∧
      Tendsto (fun k => ∫ ω, |E' k ω| ∂P)
        Filter.atTop (nhds (0 : ℝ)) := by
  refine ⟨(fun ω => |K ω|), (fun k ω => |E k ω|),
    hKI.abs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [abs_abs] using hKsmall
  · intro k
    exact (hEI k).abs
  · exact Filter.Eventually.of_forall (fun ω => abs_nonneg _)
  · intro k
    exact Filter.Eventually.of_forall (fun ω => abs_nonneg _)
  · intro k
    filter_upwards [hUpper k] with ω hω
    intro hS
    have hKle : K ω ≤ |K ω| := le_abs_self _
    have hEle : E k ω ≤ |E k ω| := le_abs_self _
    linarith only [hω hS, hKle, hEle]
  · simpa only [abs_abs] using hVan
