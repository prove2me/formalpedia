-- Prove2me | solution 2 for BookProof.HermiteRelative.norm_posL_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:11:12.031222+00:00
-- url     : https://prove2.me/submissions/959dc5f2-60e3-4866-bbeb-ada1490dd3f6

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean
Supporting proofs: ChapterHyperbolicQuadraticEsa.lean, ChapterHermiteProductBasis.lean,
ChapterYangMillsHermite.lean and ChapterNavierStokesDifferentialL2.lean, same revision. -/
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
set_option maxHeartbeats 1000000
set_option autoImplicit false
namespace BookProof.YangMillsHermite
open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert
variable {d : ℕ}
@[simp] theorem starP_add (p q : MvPolynomial (Fin d) ℂ) :
    starP (p + q) = starP p + starP q := map_add _ _ _

@[simp] theorem starP_mul (p q : MvPolynomial (Fin d) ℂ) :
    starP (p * q) = starP p * starP q := map_mul _ _ _

@[simp] theorem starP_X (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [starP]

@[simp] theorem starP_C (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c) := by
  simp [starP]

@[simp] theorem starP_zero : starP (0 : MvPolynomial (Fin d) ℂ) = 0 := map_zero _

theorem starP_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i) := map_sum _ _ _

theorem starP_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    starP (c • p) = ((starRingEnd ℂ) c) • starP p := by
  rw [smul_eq_C_mul, starP_mul, starP_C, smul_eq_C_mul]

theorem starP_real_smul (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    starP ((t : ℂ) • p) = (t : ℂ) • starP p := by
  rw [starP_smul, Complex.conj_ofReal]

theorem RealCoeff.add {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p + q) := by
  change starP (p + q) = p + q
  rw [starP_add, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.mul {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p * q) := by
  change starP (p * q) = p * q
  rw [starP_mul, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.smul {t : ℝ} {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) :
    RealCoeff ((t : ℂ) • p) := by
  rw [RealCoeff, starP_real_smul, hp]

theorem RealCoeff.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∑ i ∈ s, f i) := by
  rw [RealCoeff, starP_sum]
  exact Finset.sum_congr rfl h

theorem realCoeff_X (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ) := starP_X j

theorem eval_starP (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [starP, eval_map]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  have hev : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * q)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
        * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [map_mul, eval_starP]
  rw [hx, hev, pgFun, pgFun, gaussWD_eq_sq]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

theorem PolySym.add {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, hS, hT]

theorem PolySym.real_smul {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) :
    PolySym (((t : ℂ)) • T) := by
  intro p q
  simp only [LinearMap.smul_apply, starP_real_smul, smul_mul_assoc, mul_smul_comm]
  rw [gaussInt_smul, gaussInt_smul, hT]

theorem PolyAdj.symm_of {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : PolyAdj S T) (h' : PolyAdj T S) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, h, h']
  ring

theorem PolySym.comp_adj {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolyAdj (S.comp T) (T.comp S) := by
  intro p q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS, hT]

theorem weylProd_polySym {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T) :=
  PolySym.real_smul ((hS.comp_adj hT).symm_of (hT.comp_adj hS))

@[simp] theorem mulOp_apply (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl

theorem mulOp_polySym {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) : PolySym (mulOp f) := by
  intro p q
  simp only [mulOp_apply, starP_mul, show starP f = f from hf]
  congr 1
  ring

theorem derOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p) := rfl

theorem momOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl

theorem starP_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (pderiv j p) = pderiv j (starP p) := (MvPolynomial.pderiv_map).symm

@[simp] theorem starP_neg (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p := map_neg _ _

@[simp] theorem starP_sub (p q : MvPolynomial (Fin d) ℂ) :
    starP (p - q) = starP p - starP q := map_sub _ _ _

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h := gaussInt_add r (-s)
  rw [show (-s) = (-1 : ℂ) • s by module, gaussInt_smul] at h
  rw [show r - s = r + (-1 : ℂ) • s by module, h]
  ring

theorem gaussInt_leibniz (j : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j P * Q) + gaussInt (P * pderiv j Q) = gaussInt (X j * (P * Q)) := by
  rw [← gaussInt_pderiv j (P * Q), ← gaussInt_add]
  congr 1
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem starP_momOp (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (momOp j p)
      = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p)) := by
  rw [momOp_apply, neg_smul, starP_neg, starP_smul, starP_sub, starP_pderiv, starP_real_smul,
    starP_mul, starP_X, Complex.conj_I, neg_smul, neg_neg]

theorem momOp_polySym (j : Fin d) : PolySym (momOp (d := d) j) := by
  intro p q
  have hleib := gaussInt_leibniz j (starP p) q
  have e1 : (X j : MvPolynomial (Fin d) ℂ) * starP p * q = X j * (starP p * q) := by ring
  have e2 : starP p * (X j * q) = X j * (starP p * q) := by ring
  have hL : gaussInt (starP (momOp j p) * q)
      = Complex.I * (gaussInt (pderiv j (starP p) * q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [starP_momOp, smul_mul_assoc, gaussInt_smul, sub_mul, gaussInt_sub, smul_mul_assoc,
      gaussInt_smul, e1]
  have hR : gaussInt (starP p * momOp j q)
      = -Complex.I * (gaussInt (starP p * pderiv j q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [momOp_apply, mul_smul_comm, gaussInt_smul, mul_sub, gaussInt_sub, mul_smul_comm,
      gaussInt_smul, e2]
  rw [hL, hR]
  push_cast
  linear_combination Complex.I * hleib


end BookProof.YangMillsHermite
namespace BookProof.NavierStokesFlow.DifferentialL2
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa
variable {d : ℕ}
@[simp] theorem momPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p)) := rfl

@[simp] theorem mulXPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulXPoly i p = X i * p := rfl

theorem coreEquiv_coe (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

theorem coreOp_coreEquiv (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) : coreOp T (coreEquiv p) = coreEquiv (T p) := by
  simp [coreOp]

theorem coreOp_coe (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ((coreOp T (coreEquiv p) : polyGaussCore (d := d)) : L2d d) = pgLp (T p) := by
  rw [coreOp_coreEquiv, coreEquiv_coe]


end BookProof.NavierStokesFlow.DifferentialL2
namespace BookProof.HermiteRelative
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} {d : ℕ}
theorem coreOp_apply' (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (x : polyGaussCore (d := d)) : coreOp T x = coreEquiv (T (coreEquiv.symm x)) := rfl

theorem coreOp_add (S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (S + T) = coreOp S + coreOp T := by
  refine LinearMap.ext fun x => ?_
  simp [coreOp_apply']

theorem coreOp_smul (r : ℂ) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (r • T) = r • coreOp T := by
  refine LinearMap.ext fun x => ?_
  simp [coreOp_apply']

theorem coreOp_sum {ι : Type*} (s : Finset ι)
    (T : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (∑ i ∈ s, T i) = ∑ i ∈ s, coreOp (T i) := by
  classical
  induction s using Finset.induction with
  | empty => refine LinearMap.ext fun x => ?_; simp [coreOp_apply']
  | insert i s hi ih => rw [Finset.sum_insert hi, coreOp_add, ih, Finset.sum_insert hi]

theorem coreOp_comp (S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (S.comp T) = (coreOp S).comp (coreOp T) := by
  refine LinearMap.ext fun x => ?_
  simp [coreOp_apply']

theorem mulXPoly_eq_mulOp (i : Fin d) :
    mulXPoly i = BookProof.YangMillsHermite.mulOp (X i : MvPolynomial (Fin d) ℂ) := by
  refine LinearMap.ext fun p => ?_
  simp [BookProof.YangMillsHermite.mulOp]

theorem momPoly_eq_ymMomOp (i : Fin d) :
    momPoly i = BookProof.YangMillsHermite.momOp i := by
  refine LinearMap.ext fun p => ?_
  rw [momPoly_apply, BookProof.YangMillsHermite.momOp_apply]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  push_cast
  ring

theorem polySym_mulXPoly (i : Fin d) : BookProof.YangMillsHermite.PolySym (mulXPoly i) := by
  rw [mulXPoly_eq_mulOp]
  exact BookProof.YangMillsHermite.mulOp_polySym (BookProof.YangMillsHermite.realCoeff_X i)

theorem polySym_momPoly (i : Fin d) : BookProof.YangMillsHermite.PolySym (momPoly i) := by
  rw [momPoly_eq_ymMomOp]
  exact BookProof.YangMillsHermite.momOp_polySym i

theorem symmetricOn_of_polySym {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : BookProof.YangMillsHermite.PolySym T) :
    SymmetricOn (polyGaussCore (d := d))
      ((polyGaussCore (d := d)).subtype ∘ₗ coreOp T) := by
  intro x y
  obtain ⟨p, rfl⟩ : ∃ p, (coreEquiv (d := d)) p = x :=
    ⟨coreEquiv.symm x, coreEquiv.apply_symm_apply x⟩
  obtain ⟨q, rfl⟩ : ∃ q, (coreEquiv (d := d)) q = y :=
    ⟨coreEquiv.symm y, coreEquiv.apply_symm_apply y⟩
  have hx : (((polyGaussCore (d := d)).subtype ∘ₗ coreOp T) (coreEquiv p)) = pgLp (T p) :=
    coreOp_coe T p
  have hy : (((polyGaussCore (d := d)).subtype ∘ₗ coreOp T) (coreEquiv q)) = pgLp (T q) :=
    coreOp_coe T q
  rw [hx, hy, coreEquiv_coe, coreEquiv_coe, BookProof.YangMillsHermite.inner_pgLp_pgLp,
    BookProof.YangMillsHermite.inner_pgLp_pgLp]
  exact hT p q

theorem posL_symmetric (i : Fin d) : SymmetricOn (polyGaussCore (d := d)) (posL i) :=
  symmetricOn_of_polySym (polySym_mulXPoly i)

theorem momL_symmetric (i : Fin d) : SymmetricOn (polyGaussCore (d := d)) (momL i) :=
  symmetricOn_of_polySym (polySym_momPoly i)

theorem oscOp_eq (i : Fin d) :
    coreOp (oscPoly i) = (coreOp (momPoly i)).comp (coreOp (momPoly i))
      + (1/4 : ℂ) • ((coreOp (mulXPoly i)).comp (coreOp (mulXPoly i))) := by
  rw [oscPoly, coreOp_add, coreOp_comp, coreOp_smul, coreOp_comp]

theorem re_inner_oscL_eq (i : Fin d) (u : polyGaussCore (d := d)) :
    (inner ℂ (u : L2d d) (oscL i u) : ℂ).re
      = ‖momL i u‖ ^ 2 + ‖posL i u‖ ^ 2 / 4 := by
  have hosc : oscL i u
      = momL i (coreOp (momPoly i) u) + (1/4 : ℂ) • posL i (coreOp (mulXPoly i) u) := by
    simp [oscL, momL, posL, oscOp_eq]
  have hmom : (inner ℂ (u : L2d d) (momL i (coreOp (momPoly i) u)) : ℂ)
      = inner ℂ (momL i u) (momL i u) := by
    have h := momL_symmetric i u (coreOp (momPoly i) u)
    simpa [momL] using h.symm
  have hpos : (inner ℂ (u : L2d d) (posL i (coreOp (mulXPoly i) u)) : ℂ)
      = inner ℂ (posL i u) (posL i u) := by
    have h := posL_symmetric i u (coreOp (mulXPoly i) u)
    simpa [posL] using h.symm
  rw [hosc, inner_add_right, inner_smul_right, hmom, hpos,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]
  ring

theorem foOp_apply (b b' : Fin d → ℝ) (u : polyGaussCore (d := d)) :
    foOp b b' u = ∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u) := by
  simp only [foOp, foPoly, LinearMap.comp_apply, Submodule.subtype_apply, coreOp_sum,
    coreOp_add, coreOp_smul, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_add, Submodule.coe_smul]
  rfl

theorem gaussInt_zero : gaussInt (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  have h := gaussInt_smul (0 : ℂ) (0 : MvPolynomial (Fin d) ℂ)
  simpa using h

theorem polySym_zero : BookProof.YangMillsHermite.PolySym
    (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) := by
  intro p q
  simp [BookProof.YangMillsHermite.starP, gaussInt_zero]

theorem polySym_sum {ι : Type*} (s : Finset ι)
    (T : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (h : ∀ i ∈ s, BookProof.YangMillsHermite.PolySym (T i)) :
    BookProof.YangMillsHermite.PolySym (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using polySym_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem polySym_foPoly (b b' : Fin d → ℝ) : BookProof.YangMillsHermite.PolySym (foPoly b b') :=
  polySym_sum _ _ fun i _ =>
    (BookProof.YangMillsHermite.PolySym.real_smul (polySym_mulXPoly i)).add
      (BookProof.YangMillsHermite.PolySym.real_smul (polySym_momPoly i))

theorem foOp_symmetric (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (foOp b b') :=
  symmetricOn_of_polySym (polySym_foPoly b b')
end
end BookProof.HermiteRelative

namespace BookProof.HermiteProductBasis
open scoped ENNReal
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore
open BookProof.HermiteCore
variable {d : ℕ}
@[simp] theorem hermiteMvBasis_apply (a : Fin d →₀ ℕ) :
    hermiteMvBasis a = hermiteMvLp (d := d) a := by
  rw [hermiteMvBasis, HilbertBasis.coe_mk]

theorem pderiv_aeval_self (i : Fin d) (q : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q)
      = Polynomial.aeval (X i) (Polynomial.derivative q) := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow, map_mul,
        Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [mul_comm, mul_assoc, algebraMap_eq]

theorem pderiv_aeval_other {i j : Fin d} (h : j ≠ i) (q : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q) = 0 := by
  induction q using Polynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | monomial n c ih =>
      simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rw [Derivation.leibniz]
      simp [h, algebraMap_eq]

theorem pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by
  cases n with
  | zero => simp [hermiteFactor, hermiteCx_zero]
  | succ m =>
      rw [hermiteFactor, pderiv_aeval_self]
      have h : Polynomial.derivative (hermiteCx (m + 1)) = ((m : ℂ) + 1) • hermiteCx m := by
        have hm := congrArg (Polynomial.map (Int.castRingHom ℂ)) (derivative_hermiteZ m)
        simpa [hermiteCx, Polynomial.derivative_map, Polynomial.smul_eq_C_mul,
          Polynomial.map_mul] using hm
      rw [h]
      simp [hermiteFactor, map_smul]

theorem pderiv_hermiteFactor_other {i j : Fin d} (h : j ≠ i) (n : ℕ) :
    pderiv j (hermiteFactor i n) = 0 := pderiv_aeval_other h _

theorem pderiv_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by
  classical
  have hrest : ∀ b : Fin d →₀ ℕ, (∀ j : Fin d, j ≠ i → b j = a j) →
      ∏ j ∈ Finset.univ.erase i, hermiteFactor j (b j)
        = ∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j) :=
    fun b hb => Finset.prod_congr rfl fun j hj => by rw [hb j (Finset.ne_of_mem_erase hj)]
  have hsub : ∀ j : Fin d, j ≠ i → (a - Finsupp.single i 1 : Fin d →₀ ℕ) j = a j := by
    intro j hj; simp [Finsupp.tsub_apply, hj]
  have hsi : (a - Finsupp.single i 1 : Fin d →₀ ℕ) i = a i - 1 := by simp [Finsupp.tsub_apply]
  have hzero : pderiv i (∏ j ∈ Finset.univ.erase i, hermiteFactor j (a j)) = 0 := by
    refine Finset.prod_induction _ (fun p => pderiv i p = 0) ?_ (by simp) ?_
    · intro p q hp hq
      rw [Derivation.leibniz, hp, hq]; simp
    · intro j hj
      exact pderiv_aeval_other (Finset.ne_of_mem_erase hj).symm _
  rw [hermiteMv_erase i a, hermiteMv_erase i (a - Finsupp.single i 1), hrest _ hsub, hsi,
    Derivation.leibniz, hzero, pderiv_hermiteFactor_self]
  simp [mul_comm]

@[simp] theorem annPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    annPoly i p = pderiv i p := rfl

@[simp] theorem crePoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    crePoly i p = X i * p - pderiv i p := rfl

theorem crePoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (hermiteMv a) = hermiteMv (a + Finsupp.single i 1) := by
  rw [crePoly_apply, hermiteMv_X_mul, pderiv_hermiteMv]
  abel


end BookProof.HermiteProductBasis
namespace BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteProductCore MvPolynomial
variable {d : ℕ}
theorem pgLp_smul (r : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    pgLp (r • p) = r • pgLp p := by
  change ((coreEquiv (r • p) : polyGaussCore (d := d)) : L2d d) =
    r • ((coreEquiv p : polyGaussCore (d := d)) : L2d d)
  rw [map_smul, Submodule.coe_smul]
end BookProof.NavierStokesFlow.DifferentialL2
namespace BookProof.HyperbolicQuadratic
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
theorem momPoly_apply' (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i p = (-Complex.I) • (pderiv i p - (1/2 : ℂ) • (X i * p)) := by
  rw [momPoly_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]

theorem momPoly_sq (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (momPoly i p)
      = -(pderiv i (pderiv i p)) + (1/2 : ℂ) • p + X i * pderiv i p
        - (1/4 : ℂ) • (X i * (X i * p)) := by
  have hlei : ∀ q : MvPolynomial (Fin d) ℂ, pderiv i (X i * q) = q + X i * pderiv i q := by
    intro q
    rw [Derivation.leibniz, pderiv_X_self]
    simp [smul_eq_mul]
    ring
  set q : MvPolynomial (Fin d) ℂ := pderiv i p - (1/2 : ℂ) • (X i * p) with hq
  have h1 : momPoly i p = (-Complex.I) • q := momPoly_apply' i p
  have h2 : momPoly i ((-Complex.I) • q) = (-Complex.I) • (momPoly i q) := map_smul _ _ _
  have h3 : momPoly i q = (-Complex.I) • (pderiv i q - (1/2 : ℂ) • (X i * q)) :=
    momPoly_apply' i q
  have hdq : pderiv i q = pderiv i (pderiv i p) - (1/2 : ℂ) • (p + X i * pderiv i p) := by
    rw [hq, map_sub, Derivation.map_smul_of_tower, hlei]
  have hxq : X i * q = X i * pderiv i p - (1/2 : ℂ) • (X i * (X i * p)) := by
    rw [hq, mul_sub, mul_smul_comm]
  have hinner : pderiv i q - (1/2 : ℂ) • (X i * q)
      = pderiv i (pderiv i p) - (1/2 : ℂ) • p - X i * pderiv i p
        + (1/4 : ℂ) • (X i * (X i * p)) := by
    rw [hdq, hxq]
    module
  have hII : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by simp [Complex.I_mul_I]
  rw [h1, h2, h3, hinner, smul_smul, hII]
  module

theorem oscPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    oscPoly i p = X i * pderiv i p - pderiv i (pderiv i p) + (1/2 : ℂ) • p := by
  simp only [oscPoly, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    mulXPoly_apply, momPoly_sq]
  module

theorem hermiteMv_number (i : Fin d) (a : Fin d →₀ ℕ) :
    X i * pderiv i (hermiteMv a) - pderiv i (pderiv i (hermiteMv a))
      = ((a i : ℂ)) • hermiteMv a := by
  classical
  set b : Fin d →₀ ℕ := a - Finsupp.single i 1 with hb
  have hd : pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv b := pderiv_hermiteMv i a
  rw [hd, mul_smul_comm, Derivation.map_smul_of_tower, ← smul_sub]
  have hcre : X i * hermiteMv b - pderiv i (hermiteMv b)
      = hermiteMv (b + Finsupp.single i 1) := by
    have h := crePoly_hermiteMv i b
    rwa [crePoly_apply] at h
  rw [hcre]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
  · rw [h0]; simp
  · have hba : b + Finsupp.single i 1 = a := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [hb]; omega
      · simp [hb, hj]
    rw [hba]

theorem oscPoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    oscPoly i (hermiteMv a) = (((a i : ℝ) : ℂ) + 1/2) • hermiteMv a := by
  rw [oscPoly_apply, hermiteMv_number, ← add_smul]
  norm_num

theorem quadPoly_hermiteMv (c : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    quadPoly c (hermiteMv a) = ((quadSymbol c a : ℝ) : ℂ) • hermiteMv a := by
  rw [quadPoly, LinearMap.sum_apply]
  have hterm : ∀ i : Fin d, (((c i : ℝ) : ℂ) • oscPoly i) (hermiteMv a)
      = (((c i * ((a i : ℝ) + 1/2) : ℝ)) : ℂ) • hermiteMv a := by
    intro i
    rw [LinearMap.smul_apply, oscPoly_hermiteMv, smul_smul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul]
  congr 1
  rw [quadSymbol]
  push_cast
  ring

theorem pgLp_hermiteMvLp (a : Fin d →₀ ℕ) :
    pgLp (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a) = hermiteMvLp a := by
  rw [pgLp_smul]; rfl

theorem quadOp_hermiteMvLp (c : Fin d → ℝ) (a : Fin d →₀ ℕ)
    (h : hermiteMvLp a ∈ polyGaussCore (d := d)) :
    quadOp c ⟨hermiteMvLp a, h⟩ = ((quadSymbol c a : ℝ) : ℂ) • hermiteMvLp a := by
  have hcoe : (⟨hermiteMvLp a, h⟩ : polyGaussCore (d := d))
      = coreEquiv (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a) := by
    apply Subtype.ext
    rw [coreEquiv_coe, pgLp_hermiteMvLp]
  rw [hcoe]
  simp only [quadOp, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOp_coe, map_smul, quadPoly_hermiteMv, ← smul_assoc, smul_eq_mul, mul_comm,
    ← smul_eq_mul, smul_assoc, pgLp_smul, pgLp_hermiteMvLp]

theorem symmetricOn_of_diagonal (v : ι → E) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    {D : Submodule ℂ E} (hD : Submodule.span ℂ (Set.range v) = D)
    (T : D →ₗ[ℂ] E)
    (hT : ∀ (i : ι) (h : v i ∈ D), T ⟨v i, h⟩ = ((lam i : ℝ) : ℂ) • v i) :
    SymmetricOn D T := by
  classical
  have hvD : ∀ i, v i ∈ D := fun i => hD ▸ Submodule.subset_span ⟨i, rfl⟩
  have main : ∀ y : E, y ∈ Submodule.span ℂ (Set.range v) →
      ∀ (hy : y ∈ D) (i : ι), (inner ℂ (T ⟨v i, hvD i⟩) y : ℂ) = inner ℂ (v i) (T ⟨y, hy⟩) := by
    intro y hy0
    induction hy0 using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        intro hy i
        rw [hT i (hvD i), hT j hy, inner_smul_left, inner_smul_right,
          orthonormal_iff_ite.mp hv i j]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
    | zero =>
        intro hy i
        have h0 : (⟨(0 : E), hy⟩ : D) = 0 := Subtype.ext rfl
        simp [h0]
    | add z w hz hw ihz ihw =>
        intro hy i
        have hzD : z ∈ D := hD ▸ hz
        have hwD : w ∈ D := hD ▸ hw
        have hadd : (⟨z + w, hy⟩ : D) = ⟨z, hzD⟩ + ⟨w, hwD⟩ := Subtype.ext rfl
        rw [hadd, map_add, inner_add_right, inner_add_right, ihz hzD i, ihw hwD i]
    | smul r z hz ih =>
        intro hy i
        have hzD : z ∈ D := hD ▸ hz
        have hsm : (⟨r • z, hy⟩ : D) = r • ⟨z, hzD⟩ := Subtype.ext rfl
        rw [hsm, map_smul, inner_smul_right, inner_smul_right, ih hzD i]
  have main2 : ∀ x : E, x ∈ Submodule.span ℂ (Set.range v) →
      ∀ (hx : x ∈ D) (y : E) (hy : y ∈ D),
        (inner ℂ (T ⟨x, hx⟩) y : ℂ) = inner ℂ x (T ⟨y, hy⟩) := by
    intro x hx0
    induction hx0 using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        intro _ y hy
        exact main y (hD ▸ hy) hy j
    | zero =>
        intro hx y hy
        have h0 : (⟨(0 : E), hx⟩ : D) = 0 := Subtype.ext rfl
        simp [h0]
    | add z w hz hw ihz ihw =>
        intro hx y hy
        have hzD : z ∈ D := hD ▸ hz
        have hwD : w ∈ D := hD ▸ hw
        have hadd : (⟨z + w, hx⟩ : D) = ⟨z, hzD⟩ + ⟨w, hwD⟩ := Subtype.ext rfl
        rw [hadd, map_add, inner_add_left, inner_add_left, ihz hzD y hy, ihw hwD y hy]
    | smul r z hz ih =>
        intro hx y hy
        have hzD : z ∈ D := hD ▸ hz
        have hsm : (⟨r • z, hx⟩ : D) = r • ⟨z, hzD⟩ := Subtype.ext rfl
        rw [hsm, map_smul, inner_smul_left, inner_smul_left, ih hzD y hy]
  intro x y
  have hx : (x : E) ∈ Submodule.span ℂ (Set.range v) := hD ▸ x.2
  simpa using main2 (x : E) hx x.2 (y : E) y.2

theorem quadOp_symmetric (c : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (quadOp c) :=
  symmetricOn_of_diagonal hermiteMvLp orthonormal_hermiteMvLp (quadSymbol c)
    span_hermiteMvLp (quadOp c) (fun a h => quadOp_hermiteMvLp c a h)
end
end BookProof.HyperbolicQuadratic

namespace BookProof.HermiteRelative
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} {d : ℕ}
theorem apply_sum_of_diagonal (v : ι → E) (lam : ι → ℝ) {D : Submodule ℂ E}
    (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (s : Finset ι) (f : ι → ℂ) :
    ∀ hu : (∑ a ∈ s, f a • v a) ∈ D,
      T ⟨∑ a ∈ s, f a • v a, hu⟩ = ∑ a ∈ s, (((lam a : ℝ) : ℂ) * f a) • v a := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro hu
      have h0 : (⟨∑ a ∈ (∅ : Finset ι), f a • v a, hu⟩ : D) = 0 := Subtype.ext (by simp)
      rw [h0, map_zero, Finset.sum_empty]
  | insert a s ha ih =>
      intro hu
      have hva : f a • v a ∈ D := Submodule.smul_mem _ _ (hvD a)
      have hs : (∑ b ∈ s, f b • v b) ∈ D :=
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvD b)
      have hsplit : (⟨∑ b ∈ insert a s, f b • v b, hu⟩ : D)
          = ⟨f a • v a, hva⟩ + ⟨∑ b ∈ s, f b • v b, hs⟩ := by
        apply Subtype.ext
        simpa using Finset.sum_insert ha
      have hsm : (⟨f a • v a, hva⟩ : D) = f a • ⟨v a, hvD a⟩ := Subtype.ext rfl
      rw [hsplit, map_add, hsm, map_smul, hT a (hvD a), ih hs, Finset.sum_insert ha, smul_smul,
        mul_comm (f a)]

theorem re_inner_sum_of_diagonal (v : ι → E) (hv : Orthonormal ℂ v) (lam : ι → ℝ)
    {D : Submodule ℂ E} (hvD : ∀ a, v a ∈ D) (T : D →ₗ[ℂ] E)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (s : Finset ι) (f : ι → ℂ) (hu : (∑ a ∈ s, f a • v a) ∈ D) :
    (inner ℂ (∑ a ∈ s, f a • v a) (T ⟨∑ a ∈ s, f a • v a, hu⟩) : ℂ).re
      = ∑ a ∈ s, lam a * ‖f a‖ ^ 2 := by
  rw [apply_sum_of_diagonal v lam hvD T hT s f hu,
    hv.inner_sum f (fun a => ((lam a : ℝ) : ℂ) * f a) s, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : (starRingEnd ℂ) (f a) * (((lam a : ℝ) : ℂ) * f a)
      = ((lam a : ℝ) : ℂ) * (f a * (starRingEnd ℂ) (f a)) := by ring
  rw [h, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem re_inner_diagonal_le (v : ι → E) (hv : Orthonormal ℂ v) (lam mu : ι → ℝ)
    {D : Submodule ℂ E} (hD : Submodule.span ℂ (Set.range v) = D)
    (S T : D →ₗ[ℂ] E)
    (hS : ∀ (a : ι) (h : v a ∈ D), S ⟨v a, h⟩ = ((lam a : ℝ) : ℂ) • v a)
    (hT : ∀ (a : ι) (h : v a ∈ D), T ⟨v a, h⟩ = ((mu a : ℝ) : ℂ) • v a)
    (hle : ∀ a, lam a ≤ mu a) (u : D) :
    (inner ℂ (u : E) (S u) : ℂ).re ≤ (inner ℂ (u : E) (T u) : ℂ).re := by
  classical
  have hvD : ∀ a, v a ∈ D := fun a => hD ▸ Submodule.subset_span ⟨a, rfl⟩
  have hmem : (u : E) ∈ Submodule.span ℂ (Set.range v) := hD ▸ u.2
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hmem
  have hfu : ∑ a ∈ f.support, f a • v a = (u : E) := hf
  have husub : u = ⟨∑ a ∈ f.support, f a • v a, hfu ▸ u.2⟩ := Subtype.ext hfu.symm
  have hS' := re_inner_sum_of_diagonal v hv lam hvD S hS f.support f (hfu ▸ u.2)
  have hT' := re_inner_sum_of_diagonal v hv mu hvD T hT f.support f (hfu ▸ u.2)
  rw [husub, hS', hT']
  exact Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg ‖f a‖, hle a]

theorem le_relBound_of_sq_le {t A B c0 e : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc0 : 0 < c0) (he : 0 < e) (h : t ^ 2 ≤ (4 / c0) * (B * A)) :
    t ≤ e * A + (2 / (c0 * e)) * B := by
  have hrhs : 0 ≤ e * A + (2 / (c0 * e)) * B := by positivity
  have hsq : t ^ 2 ≤ (e * A + (2 / (c0 * e)) * B) ^ 2 := by
    have hcross : (4 / c0) * (B * A) ≤ 2 * (e * A) * ((2 / (c0 * e)) * B) := by
      have : 2 * (e * A) * ((2 / (c0 * e)) * B) = (4 / c0) * (B * A) := by
        field_simp
        ring
      rw [this]
    nlinarith [sq_nonneg (e * A), sq_nonneg ((2 / (c0 * e)) * B), h, hcross]
  nlinarith [hsq, hrhs]

theorem oscL_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ)
    (h : hermiteMvLp a ∈ polyGaussCore (d := d)) :
    oscL i ⟨hermiteMvLp a, h⟩ = (((a i : ℝ) + 1/2 : ℝ) : ℂ) • hermiteMvLp a := by
  have hcoe : (⟨hermiteMvLp a, h⟩ : polyGaussCore (d := d))
      = coreEquiv (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a) := by
    apply Subtype.ext
    rw [coreEquiv_coe, pgLp_hermiteMvLp]
  rw [hcoe]
  simp only [oscL, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coreOp_coe, map_smul, oscPoly_hermiteMv, ← smul_assoc, smul_eq_mul, mul_comm,
    ← smul_eq_mul, smul_assoc, pgLp_smul, pgLp_hermiteMvLp]
  push_cast
  ring_nf

theorem re_inner_oscL_le_quadOp (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    c0 * (inner ℂ (u : L2d d) (oscL i u) : ℂ).re
      ≤ (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re := by
  classical
  have hsymb : ∀ a : Fin d →₀ ℕ, c0 * ((a i : ℝ) + 1/2) ≤ quadSymbol c a := by
    intro a
    have hterms : ∀ j ∈ (Finset.univ : Finset (Fin d)), 0 ≤ c j * ((a j : ℝ) + 1/2) := by
      intro j _
      have : (0 : ℝ) ≤ c j := le_trans hc0.le (hc j)
      positivity
    have hle : c0 * ((a i : ℝ) + 1/2) ≤ c i * ((a i : ℝ) + 1/2) := by
      have hpos : (0 : ℝ) ≤ (a i : ℝ) + 1/2 := by positivity
      exact mul_le_mul_of_nonneg_right (hc i) hpos
    have hsum : c i * ((a i : ℝ) + 1/2) ≤ ∑ j, c j * ((a j : ℝ) + 1/2) :=
      Finset.single_le_sum hterms (Finset.mem_univ i)
    exact le_trans hle (by simpa [quadSymbol] using hsum)
  have hSdiag : ∀ (a : Fin d →₀ ℕ) (h : hermiteMvLp a ∈ polyGaussCore (d := d)),
      (((c0 : ℝ) : ℂ) • oscL i) ⟨hermiteMvLp a, h⟩
        = (((c0 * ((a i : ℝ) + 1/2) : ℝ)) : ℂ) • hermiteMvLp a := by
    intro a h
    rw [LinearMap.smul_apply, oscL_hermiteMvLp, smul_smul]
    push_cast
    ring_nf
  have hmain := re_inner_diagonal_le (hermiteMvLp (d := d)) orthonormal_hermiteMvLp
    (fun a => c0 * ((a i : ℝ) + 1/2)) (quadSymbol c) span_hermiteMvLp
    (((c0 : ℝ) : ℂ) • oscL i) (quadOp c) hSdiag (fun a h => quadOp_hermiteMvLp c a h) hsymb u
  change (inner ℂ (u : L2d d) ((c0 : ℂ) • (oscL i u))).re ≤
      (inner ℂ (u : L2d d) (quadOp c u)).re at hmain
  rw [inner_smul_right] at hmain
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hmain

theorem norm_posL_sq_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ^ 2 ≤ (4 / c0) * (‖(u : L2d d)‖ * ‖quadOp c u‖) := by
  have h1 : ‖posL i u‖ ^ 2 / 4 ≤ (inner ℂ (u : L2d d) (oscL i u) : ℂ).re := by
    rw [re_inner_oscL_eq]
    nlinarith [sq_nonneg ‖momL i u‖]
  have h2 := re_inner_oscL_le_quadOp c hc0 hc i u
  have h3 : (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ :=
    re_inner_le_norm (𝕜 := ℂ) (u : L2d d) (quadOp c u)
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, h2, h3]

theorem norm_momL_sq_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖momL i u‖ ^ 2 ≤ (4 / c0) * (‖(u : L2d d)‖ * ‖quadOp c u‖) := by
  have h1 : ‖momL i u‖ ^ 2 ≤ (inner ℂ (u : L2d d) (oscL i u) : ℂ).re := by
    rw [re_inner_oscL_eq]
    nlinarith [sq_nonneg ‖posL i u‖]
  have h2 := re_inner_oscL_le_quadOp c hc0 hc i u
  have h3 : (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ :=
    re_inner_le_norm (𝕜 := ℂ) (u : L2d d) (quadOp c u)
  have h4 : 0 ≤ ‖(u : L2d d)‖ * ‖quadOp c u‖ := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  nlinarith [mul_le_mul_of_nonneg_left h1 hc0.le, h2, h3, h4]

theorem norm_posL_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ :=
  le_relBound_of_sq_le (norm_nonneg _) (norm_nonneg _) hc0 he
    (norm_posL_sq_le c hc0 hc i u)

theorem norm_momL_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖momL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ :=
  le_relBound_of_sq_le (norm_nonneg _) (norm_nonneg _) hc0 he
    (norm_momL_sq_le c hc0 hc i u)

theorem norm_foOp_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (b b' : Fin d → ℝ) {e : ℝ} (he : 0 < e) (u : polyGaussCore (d := d)) :
    ‖foOp b b' u‖
      ≤ (∑ i, (|b i| + |b' i|)) * (e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖) := by
  classical
  set R : ℝ := e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ with hR
  have hR0 : 0 ≤ R := by
    have : 0 ≤ 2 / (c0 * e) := by positivity
    have h1 : 0 ≤ e * ‖quadOp c u‖ := by positivity
    have h2 : 0 ≤ (2 / (c0 * e)) * ‖(u : L2d d)‖ := by positivity
    linarith
  calc ‖foOp b b' u‖
      = ‖∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u)‖ := by
        rw [foOp_apply]
    _ ≤ ∑ i, ‖((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u‖ := norm_sum_le _ _
    _ ≤ ∑ i, (|b i| + |b' i|) * R := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hb : ‖((b i : ℝ) : ℂ) • posL i u‖ = |b i| * ‖posL i u‖ := by
          rw [norm_smul]
          simp
        have hb' : ‖((b' i : ℝ) : ℂ) • momL i u‖ = |b' i| * ‖momL i u‖ := by
          rw [norm_smul]
          simp
        have h1 : ‖posL i u‖ ≤ R := norm_posL_le c hc0 hc he i u
        have h2 : ‖momL i u‖ ≤ R := norm_momL_le c hc0 hc he i u
        calc ‖((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u‖
            ≤ ‖((b i : ℝ) : ℂ) • posL i u‖ + ‖((b' i : ℝ) : ℂ) • momL i u‖ := norm_add_le _ _
          _ = |b i| * ‖posL i u‖ + |b' i| * ‖momL i u‖ := by rw [hb, hb']
          _ ≤ |b i| * R + |b' i| * R := by
              have := mul_le_mul_of_nonneg_left h1 (abs_nonneg (b i))
              have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (b' i))
              linarith
          _ = (|b i| + |b' i|) * R := by ring
    _ = (∑ i, (|b i| + |b' i|)) * R := by rw [Finset.sum_mul]

theorem hermiteMvBasis_repr_quadOp (c : Fin d → ℝ) (u : polyGaussCore (d := d))
    (a : Fin d →₀ ℕ) :
    hermiteMvBasis.repr (quadOp c u) a
      = ((quadSymbol c a : ℝ) : ℂ) * hermiteMvBasis.repr (u : L2d d) a := by
  have hmem : hermiteMvLp a ∈ polyGaussCore (d := d) := hermiteMvLp_mem_core a
  have hsym := quadOp_symmetric c ⟨hermiteMvLp a, hmem⟩ u
  rw [quadOp_hermiteMvLp c a hmem, inner_smul_left, Complex.conj_ofReal] at hsym
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, hermiteMvBasis_apply]
  exact hsym.symm
end
end BookProof.HermiteRelative

open BookProof.HermiteRelative
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
variable {d : ℕ}

theorem solution (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ^ 2 ≤ (4 / c0) * (‖(u : L2d d)‖ * ‖quadOp c u‖) := by
  exact BookProof.HermiteRelative.norm_posL_sq_le c hc0 hc i u
#print axioms solution
