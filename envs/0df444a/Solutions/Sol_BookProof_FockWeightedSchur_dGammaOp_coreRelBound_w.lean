-- Prove2me | solution 1 for BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T11:13:52.35902+00:00
-- url     : https://prove2.me/submissions/a5c08267-6c28-49c8-9d68-b789c89ac84e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.dGammaOp_coreRelBound_w
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_normSq_dGamma_le_w
import Theorems.Thm_BookProof_FockWeightedSchur_diagMax_wSym_eq
import Theorems.Thm_BookProof_FockWeightedSchur_normSq_toLp_wgt
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (hw : ∀ k, 1 ≤ w k) (hherm : IsHermCol col)
    (hrow : WRowBound w col K) (hcolg : WColBound w col K) (hK0 : 0 ≤ K) :
    CoreRelBound (wSym w) (dGammaOp col) K := by

  intro x
  set u : FockAlg := fockEquiv.symm x with hu
  rw [coe_dGammaOp col x, diagMax_wSym_eq x]
  have hsq : ‖toLp (dGamma col u)‖ ^ 2 ≤ (K * ‖toLp (wgt w u)‖) ^ 2 := by
    rw [mul_pow, normSq_toLp_wgt]
    exact normSq_dGamma_le_w hw hherm hrow hcolg hK0 u
  have hR : 0 ≤ K * ‖toLp (wgt w u)‖ := mul_nonneg hK0 (norm_nonneg _)
  have hL : 0 ≤ ‖toLp (dGamma col u)‖ := norm_nonneg _
  nlinarith [hsq, hR, hL]
