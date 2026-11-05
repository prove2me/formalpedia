-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:16:24.748835+00:00
-- url     : https://prove2.me/submissions/69777aba-4672-48ff-adea-58ba058a1d5e

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.NsNonlinearFarisLavine




open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ} (S : NsSystem d)

variable {d : ℕ} (S : NsSystem d)

set_option maxHeartbeats 1000000 in
theorem solution (x : polyGaussCore (d := d)) :
    commForm (nsKoopmanOp S) (nsSquareComparison S) x
      = (gpair ((coreRepPoly d).equiv.symm x)
          (fluxPoly S * (coreRepPoly d).equiv.symm x)).re := by

  rw [← commForm_kvn_energy S x]
  exact commForm_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S) x
