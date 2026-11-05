-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:09:18.479164+00:00
-- url     : https://prove2.me/submissions/4bff21b3-fadb-4a7a-9449-2fa146eb710a

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsSquareComparison_symmetricOn
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
theorem solution :
    SymmetricOn (polyGaussCore (d := d)) (nsSquareComparison S) :=
  symmetricOn_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S)
      nsEnergyOp_symmetricOn
