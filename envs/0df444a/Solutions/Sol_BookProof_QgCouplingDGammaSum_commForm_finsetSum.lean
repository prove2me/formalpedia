-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.commForm_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:22:56.84534+00:00
-- url     : https://prove2.me/submissions/9113b058-0757-41e0-9497-d109f9c10e68

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.commForm_finsetSum
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavineCore
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D : Submodule ℂ F} (s : Finset ι) (H : ι → D →ₗ[ℂ] F) (N : D →ₗ[ℂ] F) (x : D) :
    commForm (∑ i ∈ s, H i) N x = ∑ i ∈ s, commForm (H i) N x := by

  classical
  simp only [commForm_eq, LinearMap.sum_apply, sum_inner, Complex.im_sum,
    Finset.mul_sum]
