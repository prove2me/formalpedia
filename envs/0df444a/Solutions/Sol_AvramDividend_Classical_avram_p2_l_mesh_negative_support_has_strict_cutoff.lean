-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_negative_support_has_strict_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:10:42.520467+00:00
-- url     : https://prove2.me/submissions/05accb79-0d57-4607-8764-a0cf5c29a70d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Topology

/-- A real test whose closed topological support is strictly negative
vanishes identically above a uniformly negative cutoff. -/
theorem solution (f : ℝ → ℝ)
    (hneg : tsupport f ⊆ Iio (0 : ℝ)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℝ, -ρ < z → f z = 0 := by
  have h0 : (0 : ℝ) ∈ (tsupport f)ᶜ := by
    intro hz
    exact (lt_irrefl (0 : ℝ)) (hneg hz)
  have hopen : IsOpen ((tsupport f)ᶜ) :=
    (isClosed_tsupport f).isOpen_compl
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 h0
  refine ⟨ε / 2, by positivity, ?_⟩
  intro z hz
  apply image_eq_zero_of_notMem_tsupport
  intro hzmem
  have hzneg : z < 0 := hneg hzmem
  have hzball : z ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    apply abs_lt.mpr
    constructor <;> linarith
  exact (hball hzball) hzmem
