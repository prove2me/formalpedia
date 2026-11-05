-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:12:02.014715+00:00
-- url     : https://prove2.me/submissions/aad0ae10-285e-4096-8a18-4f50316ef601

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_ge
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_quadForm
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.NsNonlinearFarisLavine




open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ} (S : NsSystem d)

variable {d : ℕ} (S : NsSystem d)

set_option maxHeartbeats 1000000 in
theorem solution (x : polyGaussCore (d := d)) :
    ‖(x : L2d d)‖ ^ 2 ≤ quadForm (nsSquareComparison S) x := by

  rw [nsSquareComparison_quadForm]
  have := nsEnergyOp_quadForm_ge x
  nlinarith [sq_nonneg ‖nsKoopmanOp S x‖]
