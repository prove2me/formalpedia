-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:05:58.205558+00:00
-- url     : https://prove2.me/submissions/3717961d-595d-4953-abec-b728e661f47f

-- Generated from ChapterQgTruncationResolvent.lean — theorem BookProof.QgTruncationResolvent.strongResolventConvergence_of_dense
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterQgTimeIndependentFlow
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTruncationResolvent



open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open BookProof.QgTruncationResolvent in
theorem solution {T : UnboundedSelfAdjoint F}
    {S : ℕ → UnboundedSelfAdjoint F} {G : Set F} (hG : Dense G)
    (h : ∀ y ∈ G, Tendsto (fun n => (S n).resCLM 1 y) atTop (𝓝 (T.resCLM 1 y))) :
    StrongResolventConvergence T S := by
  intro y
  have hb : ∀ (U : UnboundedSelfAdjoint F) (v : F), ‖U.resCLM 1 v‖ ≤ ‖v‖ := fun U v => by
    simpa using U.norm_resCLM_apply_le 1 v
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hgG⟩ := Metric.dense_iff.mp hG y (ε / 3) (by positivity)
  rw [Metric.mem_ball] at hg
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h g hgG) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_eq_norm] at h1 ⊢
  rw [dist_eq_norm] at hg
  have e : (S n).resCLM 1 y - T.resCLM 1 y = (S n).resCLM 1 (y - g)
      + ((S n).resCLM 1 g - T.resCLM 1 g) + T.resCLM 1 (g - y) := by
    simp only [map_sub]; abel
  rw [e]
  have h2 := hb (S n) (y - g)
  have h3 := hb T (g - y)
  have hyg : ‖y - g‖ < ε / 3 := by rw [norm_sub_rev]; exact hg
  have hgy : ‖g - y‖ < ε / 3 := hg
  calc _ ≤ ‖(S n).resCLM 1 (y - g)‖ + ‖(S n).resCLM 1 g - T.resCLM 1 g‖ + ‖T.resCLM 1 (g - y)‖ :=
        norm_add₃_le
    _ < ε := by linarith
