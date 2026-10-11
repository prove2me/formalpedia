-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.dGamma_finsetSum_col
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:21:56.158718+00:00
-- url     : https://prove2.me/submissions/5e1ad7b6-edc6-42c1-a5f9-492bff735f38
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.dGamma_finsetSum_col
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_finsetSum
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (s : Finset ι) (cols : ι → ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    dGamma (fun k => ∑ i ∈ s, cols i k) u = ∑ i ∈ s, dGamma (cols i) u := by

  classical
  rw [dGamma_eq_sum _ (Finset.Subset.refl (modes u))]
  have hterm : ∀ k ∈ modes u,
      creVec (∑ i ∈ s, cols i k) (annA k u) = ∑ i ∈ s, creVec (cols i k) (annA k u) :=
    fun k _ => creVec_finsetSum s (fun i => cols i k) (annA k u)
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    (dGamma_eq_sum (cols i) (Finset.Subset.refl (modes u))).symm
