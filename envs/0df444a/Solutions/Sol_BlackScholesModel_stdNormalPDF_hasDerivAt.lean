-- Prove2me | solution 1 for BlackScholesModel.stdNormalPDF_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T14:22:44.63598+00:00
-- url     : https://prove2.me/submissions/b79c16b5-b6dc-407f-a1c9-e5165bd023de

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (x : ℝ) :
    HasDerivAt stdNormalPDF (-x * stdNormalPDF x) x := by
  have hquad : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ) using 1 <;>
      first
      | rfl
      | (funext y; dsimp [id]; ring)
      | (dsimp [id]; ring)
  have hExp : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
      (Real.exp (-x ^ 2 / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x hquad
  have hPDF := hExp.const_mul (1 / Real.sqrt (2 * Real.pi))
  convert hPDF using 1 <;>
    first
    | rfl
    | (funext y; dsimp [stdNormalPDF]; ring)
    | (simp only [stdNormalPDF]; ring)