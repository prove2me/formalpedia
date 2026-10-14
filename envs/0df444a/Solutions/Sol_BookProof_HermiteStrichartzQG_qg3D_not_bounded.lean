-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.qg3D_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:09.301194+00:00
-- url     : https://prove2.me/submissions/046b87cf-b692-484a-b32a-bdc9d9848f86

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.qg3D_not_bounded
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_not_bounded
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ C : ℝ, ∀ f : hermiteCore,
      ‖qg3DHermiteHamiltonian (fun k _ => (k : ℝ)) 0 0 f‖ ≤ C * ‖(f : L2R)‖ := by

  refine hermiteCoreOp_not_bounded _ fun C => ?_
  obtain ⟨k, hk⟩ := exists_nat_gt (|C| * 16 / 3 + 16)
  refine ⟨k, ?_⟩
  have hval : qg3DModeSymbol (fun k _ => (k : ℝ)) 0 0 k = 3 / 16 * (k : ℝ) ^ 2 := by
    simp [qg3DModeSymbol, qgSymbol]
    ring
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [hval, abs_of_nonneg (by positivity)]
  nlinarith [abs_nonneg C, le_abs_self C]
