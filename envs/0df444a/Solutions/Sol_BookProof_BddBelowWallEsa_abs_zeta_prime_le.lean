-- Prove2me | solution 1 for BookProof.BddBelowWallEsa.abs_zeta_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:13:20.41909+00:00
-- url     : https://prove2.me/submissions/fb737a3a-755e-4dca-8fdb-21dbd9b28da0

-- Generated from ChapterBddBelowWallEsa.lean — solution of BookProof.BddBelowWallEsa.abs_zeta'_le
import Mathlib
import Theorems.Thm_BookProof_BddBelowWallEsa_abs_bumpG_prime_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterWeakSecondDerivative
import Definitions.Def_ChapterBddBelowWallEsa
open BookProof.BddBelowWallEsa




open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {r : ℝ} (hr : 0 < r) (x : ℝ) : |zeta' r x| ≤ bumpM / r := by

  rw [zeta', abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_bumpG'_le _) hr.le
