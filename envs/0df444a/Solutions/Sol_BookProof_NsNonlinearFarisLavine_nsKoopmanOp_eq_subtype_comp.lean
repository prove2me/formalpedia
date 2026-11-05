-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:07:37.245681+00:00
-- url     : https://prove2.me/submissions/5d855aa4-4afe-4a50-9e82-1e1cff658212

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsKoopmanOp_eq_subtype_comp
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
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
    nsKoopmanOp S = (polyGaussCore (d := d)).subtype ∘ₗ nsKoopmanCore S := rfl
