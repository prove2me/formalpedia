-- Prove2me | solution 1 for BookProof.SirkSingleTime.qgOuterFock_singleTime_shiftInvert_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-02T14:02:26.815934+00:00
-- url     : https://prove2.me/submissions/ec3faf9a-6580-4edc-8fdf-2fed138b4749
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.qgOuterFock_singleTime_shiftInvert_convergence
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_strongResAt_of_ne_zero
import Theorems.Thm_BookProof_SirkSingleTime_isShiftInvertC_neg_resCLM_shift
import Theorems.Thm_BookProof_QgTruncationResolvent_qgOuterFock_truncation_flow_convergence
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgTruncationResolvent
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgTruncationResolvent

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}
variable {Fin' : Type*} [NormedAddCommGroup Fin'] [InnerProductSpace ℂ Fin'] [CompleteSpace Fin']
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (W : WallPot) (Q : QgModeData ι)
    (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Sec ι,
              Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Sec ι) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by

  obtain ⟨T, S, hT, hS, hres, hflow⟩ := qgOuterFock_truncation_flow_convergence W Q Λ hexh
  have hres1 : StrongResAt T S 1 := fun y => hres y
  refine ⟨T, S, hT, hS, fun l hl => ⟨isShiftInvertC_neg_resCLM_shift T hl,
    fun n => isShiftInvertC_neg_resCLM_shift (S n) hl, fun u => ?_⟩, fun v t => ?_⟩
  · exact (strongResAt_of_ne_zero one_ne_zero hl hres1 u).neg
  · exact (hflow v |t| (abs_nonneg t)).2 t
