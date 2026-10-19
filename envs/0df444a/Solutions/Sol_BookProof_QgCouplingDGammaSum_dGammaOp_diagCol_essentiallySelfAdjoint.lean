-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:42:08.231319+00:00
-- url     : https://prove2.me/submissions/0f9f1834-938e-437a-82cd-11253b101291

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_diagCol_eq
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_essentiallySelfAdjoint
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}
theorem h44qg_esa_diag {κ : Type*} (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes κ)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  refine BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
    c hc (diagMax c) 1 0 0 (BookProof.NavierStokesFlow.IkebeKato.diagMax_symmetricOn c) le_rfl
    (fun x => by simp) (fun x => by simp [commForm])

theorem h44qg_esa_dGammaDiag {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (BookProof.QgCouplingDGammaSum.diagCol lam)) := by
  rw [BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq]
  exact h44qg_esa_diag _ (fun α => Finset.sum_nonneg fun k _ => mul_nonneg (hlam k) (Nat.cast_nonneg _))

theorem solution {lam : ℕ → ℝ} (hlam : ∀ k, 0 ≤ lam k) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (BookProof.QgCouplingDGammaSum.diagCol lam)) := by
  exact h44qg_esa_dGammaDiag hlam

