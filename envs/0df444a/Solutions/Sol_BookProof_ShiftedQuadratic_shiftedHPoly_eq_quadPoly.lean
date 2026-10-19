-- Prove2me | solution 1 for BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:41:09.898083+00:00
-- url     : https://prove2.me/submissions/9bfa3999-e8fd-4f4b-a660-c465392a4bfc

-- Generated from ChapterShiftedQuadraticEsa.lean — solution of BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_apply
import Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_term
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadratic




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0)
    (p : MvPolynomial (Fin d) ℂ) :
    shiftedHPoly (shiftVec c b) (boostVec c b') c b b' p
      = quadPoly c p + ((shiftConst c b b' : ℝ) : ℂ) • p := by

  rw [shiftedHPoly_apply, Finset.sum_congr rfl fun i _ => shiftedHPoly_term c b b' i (hc i) p,
    Finset.sum_add_distrib]
  congr 1
  · rw [quadPoly, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  · rw [← Finset.sum_smul, shiftConst]
    congr 1
    push_cast
    ring
