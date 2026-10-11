-- Prove2me | solution 1 for BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:43:20.117194+00:00
-- url     : https://prove2.me/submissions/79df39b3-8fb3-4b79-81fc-163229dda517

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — solution of BookProof.ShiftedQuadraticMatrix.hermiteTRLp_total
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_span_hermiteTRLp
import Theorems.Thm_BookProof_ShiftedHermiteCore_eq_zero_of_inner_coreT
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (v : L2d d) (h : ∀ α, (inner ℂ (hermiteTRLp (d := d) O a k α) v : ℂ) = 0) : v = 0 := by

  refine eq_zero_of_inner_coreT a k v fun z hz => ?_
  rw [← span_hermiteTRLp hO a k] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨α, rfl⟩ := hz; exact h α
  | zero => simp
  | add z z' _ _ ihz ihz' => rw [inner_add_left, ihz, ihz']; ring
  | smul r z _ ih => rw [inner_smul_left, ih]; ring
