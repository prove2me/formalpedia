-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-02T09:41:20.872497+00:00
-- url     : https://prove2.me/submissions/a7cc931a-7c9d-4f0c-9110-bda6267e55e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgTruncationResolvent.lean — solution of BookProof.QgTruncationResolvent.qg_truncation_hashimoto_shiftInvert_tendsto
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Theorems.Thm_BookProof_QgTruncationResolvent_qgOuterFock_truncation_flow_convergence
import Theorems.Thm_BookProof_QgTruncationResolvent_isShiftInvertC_neg_resCLM
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.QgTruncationResolvent




open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

set_option maxHeartbeats 1000000 in
theorem solution (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        IsShiftInvertC T.op Complex.I (-(T.resCLM 1)) ∧
        (∀ n, IsShiftInvertC (S n).op Complex.I (-((S n).resCLM 1))) ∧
        ∀ u : Sec ι, Tendsto (fun n => -((S n).resCLM 1 u)) atTop (𝓝 (-(T.resCLM 1 u))) := by

  obtain ⟨T, S, hT, hS, hres, -⟩ := qgOuterFock_truncation_flow_convergence W Q Λ hexh
  exact ⟨T, S, hT, hS, isShiftInvertC_neg_resCLM T, fun n => isShiftInvertC_neg_resCLM (S n),
    fun u => (hres u).neg⟩
