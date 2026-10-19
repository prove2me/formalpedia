-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotPoly_mulXPoly
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:16:59.107996+00:00
-- url     : https://prove2.me/submissions/a9ae6970-e56f-4000-9726-7cd8bcc74737

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
import Theorems.Thm_BookProof_HyperbolicQuadratic_symmetricOn_of_diagonal
import Theorems.Thm_BookProof_HyperbolicQuadratic_deficiencyTrivialAt_of_diagonal
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_hermiteTRLp_mem_coreT
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_span_hermiteTRLp
import Theorems.Thm_BookProof_ShiftedQuadraticMatrix_hermiteTRLp_total
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_ShiftedHermiteCore_polyGaussCoreT_dense
-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.rotPoly_mulXPoly
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}
theorem h44r_mulX (i : Fin d) (p : MvPolynomial (Fin d) ℂ) : mulXPoly i p = X i * p := rfl
theorem h44r_mom (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl

theorem h44r_rot_X (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    rotPoly O (X i) = ∑ j, C ((O j i : ℝ) : ℂ) * X j := by
  simp [rotPoly]

/-- chain rule -/
theorem h44r_pderiv_rot (O : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    pderiv k (rotPoly O p) = ∑ i, C ((O k i : ℝ) : ℂ) * rotPoly O (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [rotPoly]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz, hp, h44r_rot_X]
    simp only [map_sum, Derivation.leibniz, pderiv_X, pderiv_C, map_mul, map_add, smul_eq_mul,
      h44r_rot_X, mul_add, Finset.sum_add_distrib]
    simp only [Pi.single_apply, mul_zero, mul_ite, mul_one, apply_ite (rotPoly O), map_one, map_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero]
    rw [Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun _ _ => by ring

theorem h44r_rot_pderiv {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (j : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (pderiv j p) = ∑ k, C ((O k j : ℝ) : ℂ) * pderiv k (rotPoly O p) := by
  simp only [h44r_pderiv_rot, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hji : ∀ i, ∑ k, C ((O k j : ℝ) : ℂ) * (C ((O k i : ℝ) : ℂ) * rotPoly O (pderiv i p))
      = (if j = i then 1 else 0) * rotPoly O (pderiv i p) := by
    intro i
    simp only [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum]
    congr 1
    have := congrFun (congrFun hO j) i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, this]
    split_ifs <;> simp
  simp only [hji, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h44r_rot_C (O : Matrix (Fin d) (Fin d) ℝ) (a : ℂ) : rotPoly O (C a) = C a := by
  simp [rotPoly]

theorem h44r_rot_mulX (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (mulXPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • mulXPoly k (rotPoly O p) := by
  simp only [h44r_mulX, map_mul, h44r_rot_X, Finset.sum_mul, smul_eq_C_mul, mul_assoc]

theorem h44r_rot_mom {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (momPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • momPoly k (rotPoly O p) := by
  have hx := h44r_rot_mulX O i p
  simp only [h44r_mulX] at hx
  simp only [h44r_mom, map_mul, map_sub, h44r_rot_C, hx, h44r_rot_pderiv hO, smul_eq_C_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem h44r_rot_osc {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (oscPoly i p) = ∑ k, ∑ l, (((O k i * O l i : ℝ)) : ℂ) •
      (momPoly k (momPoly l (rotPoly O p)) + (1/4 : ℂ) • mulXPoly k (mulXPoly l (rotPoly O p))) := by
  simp only [oscPoly, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_add,
    map_smul, h44r_rot_mom hO, h44r_rot_mulX, map_sum, Finset.smul_sum, smul_smul,
    ← Finset.sum_add_distrib, smul_add]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  push_cast
  rw [mul_comm (1/4 : ℂ)]

theorem h44r_quadPolyMat_rot {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPolyMat (rotConj O c) (rotPoly O p) = rotPoly O (quadPoly c p) := by
  rw [quadPolyMat, quadPoly]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_sum, map_smul, h44r_rot_osc hO, Finset.smul_sum, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [rotConj]
  push_cast
  exact Finset.sum_congr rfl fun _ _ => by ring


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

theorem solution (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (mulXPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • mulXPoly k (rotPoly O p) := by
  exact h44r_rot_mulX O i p

