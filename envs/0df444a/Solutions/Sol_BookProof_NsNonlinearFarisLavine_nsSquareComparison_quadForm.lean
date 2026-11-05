-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:10:44.038263+00:00
-- url     : https://prove2.me/submissions/da4957e0-0645-4f6f-8431-9beda206505a

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsSquareComparison_quadForm
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
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
    quadForm (nsSquareComparison S) x
      = ‖nsKoopmanOp S x‖ ^ 2 + quadForm (nsEnergyOp (d := d)) x := quadForm_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S) x
