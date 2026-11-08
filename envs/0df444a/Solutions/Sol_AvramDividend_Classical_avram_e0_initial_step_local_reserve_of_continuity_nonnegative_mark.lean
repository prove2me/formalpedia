-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_initial_step_local_reserve_of_continuity_nonnegative_mark
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:48:42.469197+00:00
-- url     : https://prove2.me/submissions/3faeafb6-be94-49c7-9acb-e032c8daab8c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! A nonnegative affordable initial payment preserves the reserve near time zero.
    At zero the source reserve uses D(0)=0; at positive times it uses K. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ) (ω : Ω)
    (hKnonneg : 0 ≤ K ω)
    (hzero : X.X 0 ω = 0)
    (hcont : ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0)
    (hgap : K ω < x) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ →
      0 ≤ riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω := by
  let f : ℝ≥0 → ℝ := fun t => x + X.X t ω - K ω
  have hfcont : ContinuousAt f 0 :=
    (continuousAt_const.add hcont).sub continuousAt_const
  have hfzero : 0 < f 0 := by
    dsimp [f]
    rw [hzero]
    linarith
  have hnear : ∀ᶠ t in nhds (0 : ℝ≥0), 0 < f t :=
    hfcont.tendsto.eventually (isOpen_Ioi.mem_nhds hfzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ≥0 := ⟨ε / 2, le_of_lt (half_pos hε)⟩
  refine ⟨δ, ?_, ?_⟩
  · exact_mod_cast (half_pos hε)
  intro t ht
  by_cases htzero : t = 0
  · subst t
    have hx : 0 ≤ x := by linarith
    simpa [riskProcess, hzero] using hx
  have hdist : dist t (0 : ℝ≥0) < ε := by
    calc
      dist t (0 : ℝ≥0) = (t : ℝ) := by simp [NNReal.dist_eq]
      _ < ε / 2 := by exact_mod_cast ht
      _ < ε := half_lt_self hε
  have hft : 0 < f t := hball (Metric.mem_ball.mpr hdist)
  have heq : riskProcess X x (fun s η => if s = 0 then 0 else K η) t ω = f t := by
    simp [riskProcess, f, htzero]
  exact le_of_lt (heq.symm ▸ hft)
