-- Prove2me | solution 1 for BookProof.FockWeightedSchur.re_inner_wgt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:52:53.106548+00:00
-- url     : https://prove2.me/submissions/67392068-29fe-46de-ba7d-21896d01177a

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.re_inner_wgt
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wgt_apply
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (wgt w u)) : ℂ).re = ∑ α ∈ u.support, wSym w α * ‖u α‖ ^ 2 := by

  classical
  rw [inner_toLp u (wgt w u)]
  have hterm : ∀ α : Conf, (starRingEnd ℂ) (u α) * (wgt w u) α
      = ((wSym w α * ‖u α‖ ^ 2 : ℝ) : ℂ) := by
    intro α
    rw [wgt_apply]
    have : (starRingEnd ℂ) (u α) * u α = ((‖u α‖ ^ 2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    rw [show (starRingEnd ℂ) (u α) * ((wSym w α : ℂ) * u α)
        = (wSym w α : ℂ) * ((starRingEnd ℂ) (u α) * u α) from by ring, this]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun α _ => hterm α), ← Complex.ofReal_sum, Complex.ofReal_re]
