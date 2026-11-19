-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80c_positive_part_to_signed_mesh_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:27:28.977098+00:00
-- url     : https://prove2.me/submissions/42c23d08-05a0-402d-b572-616c4b57a183

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hI : Integrable (fun ω => max (0 : ℝ) (F ω)) P)
    (hSmall : (∫ ω, max (0 : ℝ) (F ω) ∂P) ≤ ε / 2) :
    ∃ K : Ω → ℝ, ∃ E R : ℕ → Ω → ℝ,
      Integrable K P ∧
      (∫ ω, |K ω| ∂P) ≤ ε / 2 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, R k ω ≤ 0) ∧
      (∀ k, ∀ᵐ ω ∂P, F ω ≤ K ω + E k ω + R k ω) ∧
      Tendsto (fun k => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)) := by
  refine ⟨(fun ω => max (0 : ℝ) (F ω)), (fun _ _ => (0 : ℝ)),
    (fun _ ω => F ω - max (0 : ℝ) (F ω)), hI, ?_, ?_, ?_, ?_, ?_⟩
  · convert hSmall using 1
    congr 1
    funext ω
    exact abs_of_nonneg (le_max_left (0 : ℝ) (F ω))
  · intro k
    simp
  · intro k
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp
      exact sub_nonpos.mpr (le_max_right (0 : ℝ) (F ω)))
  · intro k
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp
      linarith)
  · simp
