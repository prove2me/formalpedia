-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.coupling_esa_dGamma
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:14.855052+00:00
-- url     : https://prove2.me/submissions/7a16781a-5799-4c5e-af15-e22b9dbdb751

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.coupling_esa_dGamma
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_finsetSum_col_eq
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGammaOp_diagCol_essentiallySelfAdjoint
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {s : Finset ι} {cols : ι → ℕ → (ℕ →₀ ℂ)} {lam : ℕ → ℝ}
    (hlam : ∀ k, 0 ≤ lam k) (hdiag : (fun k => ∑ i ∈ s, cols i k) = diagCol lam) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (∑ i ∈ s, dGammaOp (cols i)) := by

  rw [← dGammaOp_finsetSum_col_eq s cols, hdiag]
  exact dGammaOp_diagCol_essentiallySelfAdjoint hlam
