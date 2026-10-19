-- Prove2me | solution 2 for BookProof.QgCouplingDGammaSum.coupling_esa_dGamma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:42:30.058071+00:00
-- url     : https://prove2.me/submissions/875dda8d-da0d-4f21-aa9c-5ffe84a259f5

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_diagCol_eq
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.coupling_esa_dGamma
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
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

theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} {lam : ℕ → ℝ}
    (hlam : ∀ k, 0 ≤ lam k) (hdiag : (fun k => ∑ i ∈ s, cols i k) = BookProof.QgCouplingDGammaSum.diagCol lam) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (∑ i ∈ s, dGammaOp (cols i)) := by
  rw [← BookProof.QgCouplingDGammaSum.dGammaOp_finsetSum_col_eq]
  have : (fun k => ∑ i ∈ s, cols i k) = BookProof.QgCouplingDGammaSum.diagCol lam := hdiag
  rw [this]
  exact h44qg_esa_dGammaDiag hlam

