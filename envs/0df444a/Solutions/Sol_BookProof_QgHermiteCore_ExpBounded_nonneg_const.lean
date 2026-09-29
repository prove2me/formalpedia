-- Prove2me | solution 1 for BookProof.QgHermiteCore.ExpBounded.nonneg_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T07:27:57.963167+00:00
-- url     : https://prove2.me/submissions/cc9a20d5-5fc8-478f-8d66-19589669b461

import Mathlib
import Definitions.Def_ChapterQgHermiteCore
open BookProof.QgHermiteCore
open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky

variable {E : Type*} [NormedAddCommGroup E]

theorem solution {f : E → ℝ} {C c : ℝ}
    (h : ∀ x, |f x| ≤ C * Real.exp (c * ‖x‖)) : 0 ≤ C := by
  have hx := h (0 : E)
  have hprod : 0 ≤ C * Real.exp (c * ‖(0 : E)‖) :=
    le_trans (abs_nonneg (f (0 : E))) hx
  have hexp : 0 < Real.exp (c * ‖(0 : E)‖) := Real.exp_pos _
  nlinarith
