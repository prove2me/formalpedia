-- Prove2me | solution 1 for BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T11:16:41.70489+00:00
-- url     : https://prove2.me/submissions/a72af0f6-5121-41bf-a212-6cb599e91c4c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.dGamma_essentiallySelfAdjointOn_core_w
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wSym_nonneg
import Theorems.Thm_BookProof_FockWeightedSchur_wcomm_nonneg
import Theorems.Thm_BookProof_FockWeightedSchur_dGammaOp_coreRelBound_w
import Theorems.Thm_BookProof_FockWeightedSchur_dGammaOp_commForm_bound_w
import Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_symmetricOn
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K)
    (hBg : WCommBound w col B) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp col) :=
  essentiallySelfAdjointOn_finiteModes_of_core_bounds (wSym w) (fun α => wSym_nonneg α)
      (dGammaOp col) K B (wcomm_nonneg hw hBg) (fun u v => dGammaOp_symmetricOn hherm u v)
      (dGammaOp_coreRelBound_w hw hherm hrow hcolg hK0) (dGammaOp_commForm_bound_w hw hherm hBg)
