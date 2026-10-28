-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.tendsto_resCLM_shift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:05:21.257457+00:00
-- url     : https://prove2.me/submissions/7017fce3-5b5c-423a-9c75-d4a598dca5fe

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.tendsto_resCLM_shift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open BookProof.QgTruncationResolvent in
theorem solution (T : UnboundedSelfAdjoint F) (S : ℕ → UnboundedSelfAdjoint F)
    {x : F} (hT : x ∈ T.domain) (hS : ∀ n, x ∈ (S n).domain)
    (hconv : Tendsto (fun n => (S n).op ⟨x, hS n⟩) atTop (𝓝 (T.op ⟨x, hT⟩))) :
    Tendsto (fun n => (S n).resCLM 1 (T.shift 1 ⟨x, hT⟩)) atTop
      (𝓝 (T.resCLM 1 (T.shift 1 ⟨x, hT⟩))) := by
  set y := T.shift 1 ⟨x, hT⟩ with hy
  have hTy : T.resCLM 1 y = x := by
    rw [UnboundedSelfAdjoint.resCLM_apply, hy, T.res_shift one_ne_zero]
  have key : ∀ n, (S n).resCLM 1 y - x
      = (S n).resCLM 1 (T.op ⟨x, hT⟩ - (S n).op ⟨x, hS n⟩) := by
    intro n
    have h1 : y = (S n).shift 1 ⟨x, hS n⟩ + (T.op ⟨x, hT⟩ - (S n).op ⟨x, hS n⟩) := by
      rw [hy, UnboundedSelfAdjoint.shift_apply, UnboundedSelfAdjoint.shift_apply]
      abel
    rw [h1, map_add, UnboundedSelfAdjoint.resCLM_apply (S n) 1 ((S n).shift 1 _),
      (S n).res_shift one_ne_zero]
    simp
  rw [hTy, tendsto_iff_norm_sub_tendsto_zero]
  have hc := (tendsto_iff_norm_sub_tendsto_zero.mp hconv)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc
  rw [key n]
  refine ((S n).norm_resCLM_apply_le 1 _).trans (le_of_eq ?_)
  rw [norm_sub_rev]; simp
