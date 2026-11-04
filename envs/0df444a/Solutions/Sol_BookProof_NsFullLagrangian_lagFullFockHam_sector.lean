-- Prove2me | solution 1 for BookProof.NsFullLagrangian.lagFullFockHam_sector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T22:36:30.665632+00:00
-- url     : https://prove2.me/submissions/7e8c291a-871c-4d01-a2fa-b02a42157148

-- Generated from ChapterNavierStokesFullLagrangianFock.lean — solution of BookProof.NsFullLagrangian.lagFullFockHam_sector
import Mathlib
import Definitions.Def_ChapterNavierStokesFullLagrangianFock
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.NsFullLagrangian




open MvPolynomial
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL BookProof.Qg3DGaugeFL
open BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore

noncomputable section

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (lam lam' mu gg : ℝ) (x : lagFockCore) (n : ℕ) :
    ((lagFullFockHam lam lam' mu gg x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n
      = lagSectorHam lam lam' mu gg n
        ⟨((x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n, x.2.2 n⟩ := rfl
