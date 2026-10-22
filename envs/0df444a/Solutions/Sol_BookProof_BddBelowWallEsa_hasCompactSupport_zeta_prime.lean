-- Prove2me | solution 1 for BookProof.BddBelowWallEsa.hasCompactSupport_zeta_prime
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T04:04:18.677606+00:00
-- url     : https://prove2.me/submissions/0cbbb17a-11b4-4862-8bb4-1a0eebdc9917

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterWeakSecondDerivative
import Mathlib
import Definitions.Def_ChapterBddBelowWallEsa
open BookProof.BddBelowWallEsa



open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

theorem solution {r : ℝ} (hr : 0 < r) : HasCompactSupport (zeta' r) := by
  have h := hasCompactSupport_bumpG'.comp_smul (inv_ne_zero hr.ne')
  have h2 := h.mul_right (f' := fun _ : ℝ => r⁻¹)
  convert h2 using 1 <;> first | rfl | (funext x; simp only [zeta', Pi.mul_apply, smul_eq_mul, div_eq_mul_inv]; ring)
