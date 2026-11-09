-- Prove2me | solution 1 for BookProof.QgTimeIndependent.qgOuterFock_timeIndependent_singleTime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:57:38.423493+00:00
-- url     : https://prove2.me/submissions/025be03e-b7a8-4023-9a43-c61d54edfb1d

-- Generated from ChapterQgTimeIndependentFlow.lean — solution of BookProof.QgTimeIndependent.qgOuterFock_timeIndependent_singleTime
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Theorems.Thm_BookProof_QgTimeIndependent_eq_prop_of_isSchrodingerSolution
import Theorems.Thm_BookProof_SirkSingleTime_qgOuterFock_singleTime_shiftInvert_convergence
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterQgTruncationResolvent
open BookProof.QgTimeIndependent




open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.EsaClosure
open BookProof.HashimotoShiftInvert
open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgTruncationResolvent
-- `qgOuterFock_singleTime_shiftInvert_convergence` is declared in this
-- namespace by its thm stub (the stub opens it; the sol did not).
open BookProof.SirkSingleTime

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (W : WallPot) (Q : QgModeData ι)
    (Λ : ℕ → Set ι) (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) :
    ∃ (T : UnboundedSelfAdjoint (Sec ι)) (S : ℕ → UnboundedSelfAdjoint (Sec ι)),
      IsSelfAdjointExtension (secHam W Q) T.op ∧
        (∀ n, IsSelfAdjointExtension (secHam W (truncModes Q (Λ n))) (S n).op) ∧
        (∀ t s : ℝ, prop T t s = T.stoneU (t - s)) ∧
        (∀ (t s : ℝ) (x : Sec ι), ‖prop T t s x‖ = ‖x‖) ∧
        (∀ (t s r : ℝ) (x : Sec ι), prop T t s (prop T s r x) = prop T t r x) ∧
        (∀ t s h : ℝ, prop T (t + h) (s + h) = prop T t s) ∧
        (∀ y : ℝ → Sec ι, IsSchrodingerSolution T y → ∀ t s : ℝ, y t = prop T t s (y s)) ∧
        (∀ l : ℝ, l ≠ 0 →
          IsShiftInvertC T.op (((l : ℝ) : ℂ) * Complex.I) (-(T.resCLM l)) ∧
            (∀ n, IsShiftInvertC (S n).op (((l : ℝ) : ℂ) * Complex.I) (-((S n).resCLM l))) ∧
            ∀ u : Sec ι,
              Tendsto (fun n => -((S n).resCLM l u)) atTop (𝓝 (-(T.resCLM l u)))) ∧
        ∀ (v : Sec ι) (t : ℝ), Tendsto (fun n => (S n).stoneU t v) atTop (𝓝 (T.stoneU t v)) := by

  obtain ⟨T, S, hT, hS, hres, hflow⟩ :=
    qgOuterFock_singleTime_shiftInvert_convergence W Q Λ hexh
  exact ⟨T, S, hT, hS, fun t s => rfl, fun t s x => norm_prop_apply T t s x,
    fun t s r x => prop_apply_prop T t s r x, fun t s h => prop_time_translation T t s h,
    fun _ hy t s => eq_prop_of_isSchrodingerSolution T hy t s, hres, hflow⟩
