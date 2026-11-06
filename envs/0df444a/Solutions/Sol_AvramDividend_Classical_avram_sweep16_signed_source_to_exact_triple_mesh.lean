-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_signed_source_to_exact_triple_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:11:37.653145+00:00
-- url     : https://prove2.me/submissions/09e08600-3539-48a4-821b-3878a5a58afd

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y M B : Ω → ℝ) (K : ℝ)
    (hM : Integrable M P ∧ (∫ ω, M ω ∂P) = 0)
    (hB : Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0)
    (hPath : ∀ᵐ ω ∂P, Y ω ≤ K + M ω + B ω) :
    ∃ Ymesh Mmesh Bmesh : ℕ → Ω → ℝ,
      ∃ M' B' DM DB : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Mmesh n) P) ∧
        (∀ n, AEStronglyMeasurable (Bmesh n) P) ∧
        Integrable DM P ∧ Integrable DB P ∧
        (∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω) ∧
        (∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M' ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B' ω))) ∧
        (∀ n, (∫ ω, Mmesh n ω ∂P) = 0) ∧
        (∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) := by
  rcases hM with ⟨hMInt, hMMean⟩
  rcases hB with ⟨hBInt, hBMean⟩
  refine ⟨(fun _ => Y), (fun _ => M), (fun _ => B),
    M, B, (fun ω => |M ω|), (fun ω => |B ω|),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hMInt.aestronglyMeasurable
  · intro n
    exact hBInt.aestronglyMeasurable
  · exact hMInt.abs
  · exact hBInt.abs
  · intro n
    filter_upwards [] with ω
    exact le_rfl
  · intro n
    filter_upwards [] with ω
    exact le_rfl
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · intro n
    exact hMMean
  · intro n
    exact hBMean
  · filter_upwards [hPath] with ω hω
    intro n
    exact hω
