-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:13:38.594871+00:00
-- url     : https://prove2.me/submissions/632797d5-6ec6-48c7-8e5d-177260b84275

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_quadForm_ge
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
    0 ≤ quadForm (nsSquareComparison S) x := le_trans (by positivity) (nsSquareComparison_quadForm_ge S x)
