-- Prove2me | solution 2 for BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:39:02.072944+00:00
-- url     : https://prove2.me/submissions/36b370e4-b4ac-449b-af76-73ae36158190

import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
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
open MeasureTheory BookProof.HermiteProductCore BookProof.QuadraticRotation in
theorem h44r_pgFun_rot {d : ℕ} {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (rotPoly O p) x = pgFun p (rotIso hO x) := by
  unfold pgFun
  congr 1
  · induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, rotPoly, MvPolynomial.aeval_X, MvPolynomial.eval_X, rotIso_apply,
        rotLin_apply, map_sum, MvPolynomial.eval_C] at hp ⊢
      push_cast at hp ⊢
      rw [hp]
  · simp only [gaussD, LinearIsometryEquiv.norm_map]
open MeasureTheory BookProof.HermiteProductCore BookProof.QuadraticRotation in
theorem h44r_inner_rot {d : ℕ} {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp (rotPoly O p)) (pgLp (rotPoly O q)) : ℂ)
      = (inner ℂ (pgLp p) (pgLp q) : ℂ) := by
  have hint : ∀ p q : MvPolynomial (Fin d) ℂ, (inner ℂ (pgLp p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * pgFun q x := by
    intro p q
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn p, pgLp_coeFn q] with x hx hy
    rw [hx, hy, RCLike.inner_apply, mul_comm]
  rw [hint, hint]
  simp_rw [h44r_pgFun_rot hO]
  exact ((rotIso hO).measurePreserving).integral_comp' (f := (rotIso hO).toHomeomorph.toMeasurableEquiv)
    (fun y : Vd d => (starRingEnd ℂ) (pgFun p y) * pgFun q y)
open BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.ShiftedHermiteCore BookProof.ShiftedQuadraticMatrix in
theorem h44r_inner_TR {d : ℕ} {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTRLp O a k α) (hermiteTRLp O a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by
  simp only [hermiteTRLp, BookProof.HermiteProductBasis.hermiteMvLp, inner_smul_left, inner_smul_right,
    inner_pgLpT, h44r_inner_rot hO]

theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (a k : Vd d) : Orthonormal ℂ (hermiteTRLp (d := d) O a k) := by
  rw [orthonormal_iff_ite]
  intro α β
  rw [h44r_inner_TR hO, orthonormal_iff_ite.mp BookProof.HermiteProductBasis.orthonormal_hermiteMvLp]

