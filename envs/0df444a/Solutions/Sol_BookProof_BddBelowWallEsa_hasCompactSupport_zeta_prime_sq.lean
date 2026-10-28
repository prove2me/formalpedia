-- Prove2me | solution 1 for BookProof.BddBelowWallEsa.hasCompactSupport_zeta_prime_sq
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T04:04:20.070036+00:00
-- url     : https://prove2.me/submissions/ed1b7cf4-07dd-4c21-b6f0-558574a9eebc

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

theorem solution {r : ℝ} (hr : 0 < r) :
    @HasCompactSupport ℝ ℝ _ instMulZeroClassOfSemiring.toZero
      (fun x => (zeta' r x) ^ 2) := by
  have h := hasCompactSupport_bumpG'.comp_smul (inv_ne_zero hr.ne')
  have h2 := (h.mul_right (f' := fun _ : ℝ => r⁻¹))
  have h3 := h2.mul_right (f' := fun x => bumpG' (r⁻¹ • x) * r⁻¹)
  convert h3 using 1 <;> first | rfl | (funext x; simp only [zeta', Pi.mul_apply, smul_eq_mul, div_eq_mul_inv]; ring)
