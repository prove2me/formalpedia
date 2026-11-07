-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T15:19:25.038584+00:00
-- url     : https://prove2.me/submissions/ef6a0ee8-ddc3-456f-b839-b17b80df8cb5

-- Generated from ChapterQgTruncationResolvent.lean — solution of BookProof.QgTruncationResolvent.starobinsky_qgContinuum_momentumCutoff_flow_convergence
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Theorems.Thm_BookProof_QgTruncationResolvent_qgOuterFock_truncation_flow_convergence
import Theorems.Thm_BookProof_QgTruncationResolvent_momWindow_exhausts
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgContinuumModeInstance
open BookProof.QgTruncationResolvent




open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
-- `CMode` lives in `BookProof.QgContinuumModeInstance`
-- (`Definitions.Def_ChapterQgContinuumModeInstance`); its published bundle was
-- compiled from the published text on 2026-11-06 and does declare it.
open BookProof.QgContinuumModeInstance

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ)
    (halpha : 0 < alpha) (g : ℝ) :
    ∃ (T : UnboundedSelfAdjoint (Sec CMode)) (S : ℕ → UnboundedSelfAdjoint (Sec CMode)),
      IsSelfAdjointExtension
          (secHam (starobinskyWall M alpha halpha) (qgContinuumModes g)) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam (starobinskyWall M alpha halpha)
          (truncModes (qgContinuumModes g) (momWindow n))) (S n).op) ∧
        StrongResolventConvergence T S ∧
        ∀ (v : Sec CMode) (T₀ : ℝ), 0 ≤ T₀ →
          TendstoUniformlyOn (fun n t => (S n).stoneU t v) (fun t => T.stoneU t v) atTop
              (Set.Icc (-T₀) T₀) ∧
            ∀ t : ℝ, Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) :=
  qgOuterFock_truncation_flow_convergence (starobinskyWall M alpha halpha)
      (qgContinuumModes g) momWindow momWindow_exhausts
