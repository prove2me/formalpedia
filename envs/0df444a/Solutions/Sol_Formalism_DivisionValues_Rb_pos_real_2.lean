-- Prove2me | solution 2 for Formalism.DivisionValues.Rb.pos_real
-- status  : ACCEPTED   (prove)
-- author  : @narumi
-- created : 2026-11-23T14:37:44.182574+00:00
-- url     : https://prove2.me/submissions/786ba996-f87a-4d75-97ed-51dd5d70ce76

import Mathlib.Analysis.Complex.Order

set_option autoImplicit false
open scoped ComplexOrder

theorem solution {z : ℂ} (h : 0 < z) : z = ((z.re : ℝ) : ℂ) ∧ 0 < z.re := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp h
  refine ⟨Complex.ext ?_ ?_, hre⟩
  · simp
  · simpa using him.symm
