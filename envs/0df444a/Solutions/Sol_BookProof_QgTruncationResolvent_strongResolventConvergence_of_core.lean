-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.strongResolventConvergence_of_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T05:58:59.536324+00:00
-- url     : https://prove2.me/submissions/083432f9-d8e4-4084-8da4-ff552c99b0c9

-- Generated from ChapterQgTruncationResolvent.lean — solution of BookProof.QgTruncationResolvent.strongResolventConvergence_of_core
import Mathlib
import Definitions.Def_ChapterQgTruncationResolvent
import Theorems.Thm_BookProof_QgTruncationResolvent_strongResolventConvergence_of_dense
import Theorems.Thm_BookProof_QgTruncationResolvent_tendsto_resCLM_shift
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
open BookProof.QgTruncationResolvent




open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.QgOuterFockCoreFL BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.ScalaronEsa BookProof.DirectSumEsa
open BookProof.EsaClosure
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {Hn : ℕ → (D →ₗ[ℂ] F)} {T : UnboundedSelfAdjoint F} {S : ℕ → UnboundedSelfAdjoint F}
    (hesa : EssentiallySelfAdjointOn D Hc) (hT : IsSelfAdjointExtension Hc T.op)
    (hS : ∀ n, IsSelfAdjointExtension (Hn n) (S n).op)
    (hconv : ∀ x : D, Tendsto (fun n => Hn n x) atTop (𝓝 (Hc x))) :
    StrongResolventConvergence T S := by

  have hmemT : ∀ x : D, (x : F) ∈ T.domain := fun x => (hT.1 x).choose
  have hopT : ∀ x : D, T.op ⟨(x : F), hmemT x⟩ = Hc x := fun x => (hT.1 x).choose_spec
  have hmemS : ∀ (n : ℕ) (x : D), (x : F) ∈ (S n).domain := fun n x => ((hS n).1 x).choose
  have hopS : ∀ (n : ℕ) (x : D), (S n).op ⟨(x : F), hmemS n x⟩ = Hn n x :=
    fun n x => ((hS n).1 x).choose_spec
  set Phi : D →ₗ[ℂ] F :=
    (T.shift 1).comp (Submodule.inclusion (fun x hx => hmemT ⟨x, hx⟩)) with hPhi
  have hPhi_apply : ∀ x : D, Phi x = T.shift 1 ⟨(x : F), hmemT x⟩ := fun _ => rfl
  have hdense : Dense ((LinearMap.range Phi : Submodule ℂ F) : Set F) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    have hzero : ∀ v : D, (inner ℂ (Phi v) w : ℂ) = 0 := fun v =>
      (Submodule.mem_orthogonal _ _).mp hw (Phi v) ⟨v, rfl⟩
    refine hesa.2 w fun v => ?_
    have h := hzero v
    rw [hPhi_apply v, UnboundedSelfAdjoint.shift_apply, hopT v] at h
    have h2 : (inner ℂ (Hc v) w : ℂ) - (inner ℂ (((1 : ℝ) * Complex.I : ℂ) • (v : F)) w : ℂ)
        = 0 := by rw [← inner_sub_left]; exact h
    rw [inner_smul_left] at h2
    simp only [Complex.ofReal_one, one_mul, Complex.conj_I] at h2 ⊢
    linear_combination h2
  refine strongResolventConvergence_of_dense hdense ?_
  rintro y ⟨v, rfl⟩
  rw [hPhi_apply v]
  refine tendsto_resCLM_shift T S (hmemT v) (fun n => hmemS n v) ?_
  rw [hopT v]
  simpa only [hopS] using hconv v
