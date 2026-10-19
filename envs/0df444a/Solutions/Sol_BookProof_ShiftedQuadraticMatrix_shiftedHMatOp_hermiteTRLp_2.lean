-- Prove2me | solution 2 for BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:06:07.249779+00:00
-- url     : https://prove2.me/submissions/94bbd1f3-da0b-465c-8fac-437bfcd7eb69

import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_HyperbolicQuadratic_quadPoly_hermiteMv
-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
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

open BookProof.ShiftedHermiteCore BookProof.NavierStokesFlow.DifferentialL2 MvPolynomial in
theorem h44x_term {d : ℕ} (a k : BookProof.HermiteProductCore.Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (p q : Fin d)
    (f : MvPolynomial (Fin d) ℂ) :
    ((A p q : ℝ) : ℂ) • ((momTPoly k p).comp (momTPoly k q) f
        + (1/4 : ℂ) • ((mulXTPoly a p).comp (mulXTPoly a q) f))
      = ((A p q : ℝ) : ℂ) • (momPoly p (momPoly q f) + (1/4 : ℂ) • (X p * (X q * f)))
        + ((A p q * k q : ℝ) : ℂ) • momPoly p f + ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f) + ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by
  simp only [momTPoly, mulXTPoly, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
  simp only [h44r_mulX]
  push_cast
  module
open BookProof.ShiftedHermiteCore BookProof.NavierStokesFlow.DifferentialL2 MvPolynomial BookProof.ShiftedQuadraticMatrix BookProof.QuadraticRotation in
theorem h44x_quadT {d : ℕ} (a k : BookProof.HermiteProductCore.Vd d) (A : Matrix (Fin d) (Fin d) ℝ)
    (f : MvPolynomial (Fin d) ℂ) :
    quadPolyMatT a k A f
      = quadPolyMat A f
        + ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
        + ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
        + ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by
  rw [quadPolyMatT, quadPolyMat]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, h44x_term]
  simp only [LinearMap.comp_apply, h44r_mulX, Finset.sum_add_distrib]
open BookProof.ShiftedHermiteCore BookProof.NavierStokesFlow.DifferentialL2 MvPolynomial BookProof.ShiftedQuadraticMatrix in
theorem h44x_fo {d : ℕ} (a k : BookProof.HermiteProductCore.Vd d) (b b' : Fin d → ℝ) (f : MvPolynomial (Fin d) ℂ) :
    foTPoly a k b b' f
      = ∑ i, ((b i : ℝ) : ℂ) • (X i * f) + ∑ i, ((b' i : ℝ) : ℂ) • momPoly i f
        + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f := by
  rw [foTPoly]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, momTPoly, mulXTPoly,
    LinearMap.id_apply, h44r_mulX, smul_add, smul_smul]
  push_cast
  simp only [Finset.sum_smul, add_smul, Finset.sum_add_distrib]
  abel
open BookProof.ShiftedQuadraticMatrix BookProof.QuadraticRotation in
theorem h44x_HMat_eq (a k : Vd d) {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : ∀ i j, A i j = A j i) (b b' : Fin d → ℝ)
    (ha : ∀ i, ∑ j, A i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, A i j * k j = -(b' i) / 2)
    (f : MvPolynomial (Fin d) ℂ) :
    shiftedHMatPoly a k A b b' f
      = quadPolyMat A f + ((matShiftConst a k b b' : ℝ) : ℂ) • f := by
  rw [shiftedHMatPoly, LinearMap.add_apply, h44x_quadT, h44x_fo]
  have h1 : ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
      = (-(1/2) : ℂ) • ∑ p, ((b' p : ℝ) : ℂ) • momPoly p f := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_smul, smul_smul, ← Complex.ofReal_sum, hk p]
    congr 1; push_cast; ring
  have h2 : ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
      = (-(1/2) : ℂ) • ∑ p, ((b' p : ℝ) : ℂ) • momPoly p f := by
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_smul, smul_smul, ← Complex.ofReal_sum]
    simp_rw [hsym _ p]
    rw [hk p]
    congr 1; push_cast; ring
  have h3 : ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
      = (-(1/2) : ℂ) • ∑ p, ((b p : ℝ) : ℂ) • (X p * f) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_smul, smul_smul, ← Complex.ofReal_sum, ← Finset.sum_div, ha p]
    congr 1; push_cast; ring
  have h4 : ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
      = (-(1/2) : ℂ) • ∑ p, ((b p : ℝ) : ℂ) • (X p * f) := by
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_smul, smul_smul, ← Complex.ofReal_sum, ← Finset.sum_div]
    simp_rw [hsym _ p]
    rw [ha p]
    congr 1; push_cast; ring
  have e1 : ∀ p, ∑ q, A p q * (k p * k q + a p * a q / 4)
      = k p * (∑ q, A p q * k q) + a p * (∑ q, A p q * a q) / 4 := by
    intro p
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hr : ∑ p, ∑ q, A p q * (k p * k q + a p * a q / 4) + ∑ i, (b i * a i + b' i * k i)
      = matShiftConst a k b b' := by
    simp only [e1, ha, hk, matShiftConst]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun q _ => by ring
  have h5 : ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f
      + ((∑ i, (b i * a i + b' i * k i) : ℝ) : ℂ) • f = ((matShiftConst a k b b' : ℝ) : ℂ) • f := by
    rw [← hr]
    simp only [← Finset.sum_smul, ← Complex.ofReal_sum, ← add_smul, Complex.ofReal_add]
  rw [h1, h2, h3, h4, ← h5]
  module


theorem h44r_coreEquivT_coe (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquivT a k p : polyGaussCoreT a k) : L2d d) = pgLpT a k p := rfl

theorem h44r_eig {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    (α : Fin d →₀ ℕ) (h : hermiteTRLp O a k α ∈ polyGaussCoreT a k) :
    shiftedHMatOp a k (rotConj O c) b b' ⟨_, h⟩
      = (((quadSymbol c α + matShiftConst a k b b' : ℝ)) : ℂ) • hermiteTRLp O a k α := by
  have hx : (⟨hermiteTRLp O a k α, h⟩ : polyGaussCoreT a k)
      = coreEquivT a k ((((hermiteMvNorm α : ℝ) : ℂ)⁻¹) • rotPoly O (hermiteMv α)) := by
    apply Subtype.ext
    rw [h44r_coreEquivT_coe, ← pgMapT_apply, map_smul, pgMapT_apply]
    rfl
  rw [hx]
  simp only [shiftedHMatOp, coreOpT, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
  rw [map_smul, h44x_HMat_eq a k hsym b b' ha hk, h44r_quadPolyMat_rot hO, quadPoly_hermiteMv,
    h44r_coreEquivT_coe, hermiteTRLp, ← pgMapT_apply, ← pgMapT_apply]
  simp only [map_smul, map_add, smul_smul, ← add_smul]
  push_cast
  congr 1
  ring

theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    (α : Fin d →₀ ℕ) (h : hermiteTRLp O a k α ∈ polyGaussCoreT a k) :
    shiftedHMatOp a k (rotConj O c) b b' ⟨_, h⟩
      = (((quadSymbol c α + matShiftConst a k b b' : ℝ)) : ℂ) • hermiteTRLp O a k α := by
  exact h44r_eig hO c a k b b' hsym ha hk α h

