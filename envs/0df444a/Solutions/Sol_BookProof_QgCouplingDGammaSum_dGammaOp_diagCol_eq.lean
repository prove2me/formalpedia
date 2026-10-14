-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T06:21:22.628655+00:00
-- url     : https://prove2.me/submissions/b1564609-9e6e-4dd0-9454-c6d5d0d0fee9

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.dGammaOp_diagCol_eq
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_dGamma_diagCol_apply
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
import Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs
open BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) :
    dGammaOp (diagCol lam)
      = (diagMax (occEnergy lam)).comp
          (Submodule.inclusion (finiteModes_le_maxDom (occEnergy lam))) := by

  refine LinearMap.ext fun x => ?_
  refine lp.ext (funext fun α => ?_)
  have hx : ((x : lpFiniteModes Conf) : Fock) = toLp (fockEquiv.symm x) := coe_fockEquiv_symm x
  have hxα : ((x : lpFiniteModes Conf) : Fock) α = (fockEquiv.symm x) α := by
    rw [hx]; rfl
  rw [coe_dGammaOp]
  change (dGamma (diagCol lam) (fockEquiv.symm x)) α = _
  rw [dGamma_diagCol_apply]
  change ((occEnergy lam α : ℝ) : ℂ) * (fockEquiv.symm x) α
      = ((occEnergy lam α : ℝ) : ℂ) * (((x : lpFiniteModes Conf) : Fock) : Conf → ℂ) α
  rw [hxα]
