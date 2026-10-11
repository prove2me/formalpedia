-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.dGammaOp_add_col
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:12.806736+00:00
-- url     : https://prove2.me/submissions/1769dee8-d8dd-4546-9211-fe51b36612d7

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.dGammaOp_add_col
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_add
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum
import Theorems.Thm_BookProof_FockSecondQuantization_toLpL_apply
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
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
theorem solution (a b : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp (fun k => a k + b k) x = dGammaOp a x + dGammaOp b x := by

  rw [coe_dGammaOp, coe_dGammaOp, coe_dGammaOp,
    dGamma_eq_sum _ (Finset.Subset.refl (modes (fockEquiv.symm x))),
    dGamma_eq_sum a (Finset.Subset.refl (modes (fockEquiv.symm x))),
    dGamma_eq_sum b (Finset.Subset.refl (modes (fockEquiv.symm x))),
    ← toLpL_apply, ← toLpL_apply, ← toLpL_apply, ← map_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => creVec_add (a k) (b k) _
