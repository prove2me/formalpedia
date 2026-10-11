-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:07:18.989515+00:00
-- url     : https://prove2.me/submissions/2a17b8ac-c3bd-4fd2-9a15-9a586e30d872
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.halfLineFullData_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiagOp_sum
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_weyl_momOp_diagOp
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_halfLineFullData_advection
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin 15 → ℕ → ℝ) (nu : ℝ) :
    (halfLineFullData c nu).hamiltonian = tridiagOp (nsCoupling (halfLineSymbol c nu)) := by

  have h : ∀ i : Fin 3,
      ((halfLineFullData c nu).mom i).comp ((halfLineFullData c nu).advection i)
        + ((halfLineFullData c nu).advection i).comp ((halfLineFullData c nu).mom i)
        = tridiagOp (nsCoupling (halfLineAlpha c nu i)) := by
    intro i
    rw [halfLineFullData_advection]
    exact weyl_momOp_diagOp _
  rw [NSFullData.hamiltonian, Finset.sum_congr rfl (fun i _ => h i)]
  show (∑ i, tridiagOp (nsCoupling (halfLineAlpha c nu i)))
      = tridiagOp (nsCoupling (halfLineSymbol c nu))
  rw [tridiagOp_sum]
  congr 1
  funext n
  simp only [nsCoupling, halfLineSymbol, Complex.ofReal_sum]
  rw [show (∑ i : Fin 3, ((halfLineAlpha c nu i n : ℝ) : ℂ))
        + (∑ i : Fin 3, ((halfLineAlpha c nu i (n + 1) : ℝ) : ℂ))
      = ∑ i : Fin 3, (((halfLineAlpha c nu i n : ℝ) : ℂ)
          + ((halfLineAlpha c nu i (n + 1) : ℝ) : ℂ)) from Finset.sum_add_distrib.symm,
    Finset.mul_sum]
