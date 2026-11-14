-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:15.032785+00:00
-- url     : https://prove2.me/submissions/4ca412da-25c1-4a5c-94f9-3a36f8154579

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (B : ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
        |z - y| < δ → |w z - w y| < ε := by
  have hw_closed : ContinuousOn w (Icc (0 : ℝ) B) :=
    hw_cont.mono (fun z hz => hz.1)
  have hUC : UniformContinuousOn w (Icc (0 : ℝ) B) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hw_closed
  intro ε hε
  obtain ⟨δ, hδ, hδimpl⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy z hz hdiff
  have hdist : dist y z < δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using hdiff
  have hvalue := hδimpl y hy z hz hdist
  simpa only [Real.dist_eq, abs_sub_comm] using hvalue
