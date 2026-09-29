-- Prove2me | solution 1 for BookProof.HermiteRelative.quadOp_add_firstOrder_essentiallySelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:18:40.177893+00:00
-- url     : https://prove2.me/submissions/076af58b-5637-481d-8e16-a6c6574e39c7

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean
Supporting complete proofs from ChapterHyperbolicQuadraticEsa.lean, ChapterHermiteProductBasis.lean,
ChapterYangMillsHermite.lean, ChapterNavierStokesDifferentialL2.lean, ChapterFarisLavine.lean,
ChapterKatoRellichDeficiency.lean, and ChapterKatoRellichRelative.lean in the same revision. -/
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

namespace BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

theorem inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [inner_im_swap (T x) (x : F)] at h
  linarith

theorem norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring

theorem dense_range_of_deficiencyTrivialAt [CompleteSpace F] (H : D →ₗ[ℂ] F) (w₀ : ℂ)
    (h : DeficiencyTrivialAt D H (starRingEnd ℂ w₀)) :
    Dense (Set.range fun x : D => H x - w₀ • (x : F)) := by
  set K : Submodule ℂ F := LinearMap.range (H - w₀ • D.subtype) with hK
  have hset : (K : Set F) = Set.range fun x : D => H x - w₀ • (x : F) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
  rw [← hset, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  refine h f fun v => ?_
  have hv := (Submodule.mem_orthogonal K f).mp hf (H v - w₀ • (v : F))
    ⟨v, by simp [LinearMap.sub_apply]⟩
  rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hv
  exact hv

theorem exists_weak_graph_limit [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (d : ℝ) (hd : d ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)))
    (y : F) :
    ∃ u z : F, (∀ v : D, (inner ℂ (H v) u : ℂ) = inner ℂ (v : F) z) ∧
      z - ((d : ℂ) * Complex.I) • u = y ∧ (inner ℂ z u : ℂ).im = 0 := by
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hchoice : ∀ n : ℕ, ∃ x : D, ‖(H x - ((d : ℂ) * Complex.I) • (x : F)) - y‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨p, hp1, x, hx⟩ := Metric.dense_iff.mp hdense y (1 / (n + 1)) hpos
    refine ⟨x, ?_⟩
    rw [← hx] at hp1
    simpa [dist_eq_norm] using hp1
  choose x hx using hchoice
  set Y : ℕ → F := fun n => H (x n) - ((d : ℂ) * Complex.I) • ((x n : F)) with hY
  have hYtend : Filter.Tendsto Y Filter.atTop (nhds y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hYcauchy : CauchySeq Y := hYtend.cauchySeq
  have hest : ∀ m n : ℕ, |d| * ‖(x m : F) - (x n : F)‖ ≤ ‖Y m - Y n‖ ∧
      ‖H (x m) - H (x n)‖ ≤ ‖Y m - Y n‖ := by
    intro m n
    have hsplit : Y m - Y n = H (x m - x n) - ((d : ℂ) * Complex.I) • ((x m - x n : D) : F) := by
      simp [hY, map_sub, smul_sub]
      abel
    have hsq := norm_sub_smul_sq H hH d (x m - x n)
    rw [← hsplit] at hsq
    have hcoe : ((x m - x n : D) : F) = (x m : F) - (x n : F) := rfl
    rw [hcoe, map_sub] at hsq
    constructor
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_abs d, sq_nonneg (‖H (x m) - H (x n)‖)]
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_nonneg d, sq_nonneg (d * ‖(x m : F) - (x n : F)‖)]
  have hxcauchy : CauchySeq (fun n => (x n : F)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy (ε * |d|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).1
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    nlinarith
  have hHxcauchy : CauchySeq (fun n => H (x n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).2
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    linarith
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hxcauchy
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hHxcauchy
  refine ⟨u, z, ?_, ?_, ?_⟩
  · intro v
    have h1 : Filter.Tendsto (fun n => (inner ℂ (H v) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ (H v) u)) := Filter.Tendsto.inner tendsto_const_nhds hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (v : F) (H (x n)) : ℂ)) Filter.atTop
        (nhds (inner ℂ (v : F) z)) := Filter.Tendsto.inner tendsto_const_nhds hz
    have heq : ∀ n, (inner ℂ (H v) (x n : F) : ℂ) = inner ℂ (v : F) (H (x n)) := fun n => hH v (x n)
    exact tendsto_nhds_unique (by simpa [heq] using h1) h2
  · have hlim : Filter.Tendsto Y Filter.atTop (nhds (z - ((d : ℂ) * Complex.I) • u)) := by
      simpa [hY] using hz.sub (Filter.Tendsto.const_smul hu ((d : ℂ) * Complex.I))
    exact tendsto_nhds_unique hlim hYtend
  · have h1 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ z u)) := Filter.Tendsto.inner hz hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ).im) Filter.atTop
        (nhds ((inner ℂ z u : ℂ).im)) := (Complex.continuous_im.tendsto _).comp h1
    have h3 : ∀ n, (inner ℂ (H (x n)) (x n : F) : ℂ).im = 0 :=
      fun n => inner_apply_self_im H hH (x n)
    simp only [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds

theorem deficiencyTrivialAt_of_dense_range [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (e : ℝ) (he : e ≠ 0) (σ : ℂ) (hσ : σ.im ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F)))
    (hdef : DeficiencyTrivialAt D H ((e : ℂ) * Complex.I)) :
    DeficiencyTrivialAt D H σ := by
  intro w hw
  obtain ⟨u, z, hu, hzy, him⟩ :=
    exists_weak_graph_limit H hH e he hdense ((σ - (e : ℂ) * Complex.I) • w)
  have hzeq : z = ((e : ℂ) * Complex.I) • u + (σ - (e : ℂ) * Complex.I) • w := by
    rw [← hzy]; abel
  have hs : ∀ v : D, (inner ℂ (H v) (w - u) : ℂ)
      = ((e : ℂ) * Complex.I) * inner ℂ (v : F) (w - u) := by
    intro v
    rw [inner_sub_right, inner_sub_right, hw v, hu v, hzeq, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  have hwu : w = u := sub_eq_zero.mp (hdef (w - u) hs)
  have hzs : z = σ • w := by rw [hzeq, ← hwu]; module
  have hinner : (inner ℂ z u : ℂ) = starRingEnd ℂ σ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [hzs, ← hwu, inner_smul_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hinner, Complex.mul_im] at him
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.conj_im, mul_zero, zero_add] at him
  have hnorm : ‖w‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd (by linarith [neg_eq_zero.mp h] : σ.im = 0) hσ
    · exact h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])
end BookProof.FarisLavine
namespace BookProof.KatoRellich
open BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem deficiencyTrivialAt_of_dense (T : D →ₗ[ℂ] F) (z : ℂ)
    (hd : Dense (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  have hclosed : IsClosed {y : F | (inner ℂ y w : ℂ) = 0} :=
    isClosed_eq (Continuous.inner continuous_id continuous_const) continuous_const
  have hsub : (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))
      ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := by
    rintro _ ⟨x, rfl⟩
    simp only [Set.mem_setOf_eq, inner_sub_left, inner_smul_left, hw x, Complex.conj_conj]
    ring
  have huniv := hclosed.closure_subset_iff.mpr hsub
  rw [hd.closure_eq] at huniv
  exact inner_self_eq_zero.mp (huniv (Set.mem_univ w))

theorem symmetricOn_add {H B : D →ₗ[ℂ] F} (hH : SymmetricOn D H) (hB : SymmetricOn D B) :
    SymmetricOn D (H + B) := by
  intro x y
  simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hH x y, hB x y]

theorem norm_le_of_relBound (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : e ≠ 0)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) (x : D) :
    ‖B x‖ ≤ (a + b / |e|) * ‖H x - ((e : ℂ) * Complex.I) • (x : F)‖ := by
  have he0 : (0 : ℝ) < |e| := abs_pos.mpr he
  set N : ℝ := ‖H x - ((e : ℂ) * Complex.I) • (x : F)‖ with hN
  have hsq : N ^ 2 = ‖H x‖ ^ 2 + e ^ 2 * ‖(x : F)‖ ^ 2 := norm_sub_smul_sq H hH e x
  have hN0 : 0 ≤ N := norm_nonneg _
  have h1 : ‖H x‖ ≤ N := by
    nlinarith [norm_nonneg (H x), sq_nonneg (e * ‖(x : F)‖), norm_nonneg (x : F),
      sq_nonneg ‖(x : F)‖]
  have h2 : |e| * ‖(x : F)‖ ≤ N := by
    nlinarith [norm_nonneg (H x), norm_nonneg (x : F), sq_abs e,
      mul_nonneg (abs_nonneg e) (norm_nonneg (x : F))]
  have h3 : b * ‖(x : F)‖ ≤ (b / |e|) * N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ he0]
    nlinarith
  calc ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖ := hrel x
    _ ≤ a * N + (b / |e|) * N := by nlinarith
    _ = (a + b / |e|) * N := by ring

theorem dense_range_add_relBounded (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : e ≠ 0)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) (hq1 : a + b / |e| < 1)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F))) :
    Dense (Set.range fun x : D => (H x + B x) - ((e : ℂ) * Complex.I) • (x : F)) := by
  have he0 : (0 : ℝ) < |e| := abs_pos.mpr he
  set lam : ℂ := (e : ℂ) * Complex.I with hlam
  set q : ℝ := a + b / |e| with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hBq : ∀ x : D, ‖B x‖ ≤ q * ‖H x - lam • (x : F)‖ :=
    norm_le_of_relBound H B hH ha hb he hrel
  rw [Metric.dense_iff]
  intro y r hr
  obtain ⟨n, hn0⟩ : ∃ n : ℕ, q ^ n < (r / 2) / (‖y‖ + 1) :=
    exists_pow_lt_of_lt_one (by positivity) hq1
  have hn : q ^ n * ‖y‖ < r / 2 := by
    have h1 : q ^ n * ‖y‖ ≤ q ^ n * (‖y‖ + 1) := by
      have := pow_nonneg hq0 n
      nlinarith [norm_nonneg y]
    have h2 : q ^ n * (‖y‖ + 1) < ((r / 2) / (‖y‖ + 1)) * (‖y‖ + 1) := by
      have : (0 : ℝ) < ‖y‖ + 1 := by positivity
      exact mul_lt_mul_of_pos_right hn0 this
    have h3 : ((r / 2) / (‖y‖ + 1)) * (‖y‖ + 1) = r / 2 := by field_simp
    linarith
  set δ : ℝ := r / (4 * (n + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have step : ∀ v : F, ∃ x : D, ‖(H x - lam • (x : F)) - v‖ < δ := by
    intro v
    obtain ⟨z, hz1, x, hx⟩ := (Metric.dense_iff.mp hdense) v δ hδ
    have hx' : H x - lam • (x : F) = z := hx
    exact ⟨x, by rw [hx']; simpa [dist_eq_norm] using hz1⟩
  choose pick hpick using step
  set rr : ℕ → F := fun k => Nat.rec y (fun _ p => -(B (pick p))) k with hrrdef
  have hrr0 : rr 0 = y := rfl
  have hrrs : ∀ k, rr (k + 1) = -(B (pick (rr k))) := fun _ => rfl
  set v : ℕ → D := fun k => pick (rr k) with hvdef
  set S : ℕ → D := fun m => ∑ k ∈ Finset.range m, v k with hSdef
  have hrrbound : ∀ k, ‖rr k‖ ≤ q ^ k * ‖y‖ + k * δ := by
    intro k
    induction k with
    | zero => simp [hrr0]
    | succ k ih =>
      have h1 : ‖rr (k + 1)‖ ≤ q * ‖H (v k) - lam • (v k : F)‖ := by
        rw [hrrs k, norm_neg]
        exact hBq (v k)
      have hstep : ‖(H (v k) - lam • (v k : F)) - rr k‖ < δ := hpick (rr k)
      have h3 : ‖H (v k) - lam • (v k : F)‖ ≤ ‖rr k‖ + δ := by
        have heq : H (v k) - lam • (v k : F)
            = ((H (v k) - lam • (v k : F)) - rr k) + rr k := by abel
        rw [heq]
        calc ‖((H (v k) - lam • (v k : F)) - rr k) + rr k‖
            ≤ ‖(H (v k) - lam • (v k : F)) - rr k‖ + ‖rr k‖ := norm_add_le _ _
          _ ≤ δ + ‖rr k‖ := by linarith
          _ = ‖rr k‖ + δ := by ring
      have h4 : q * ‖H (v k) - lam • (v k : F)‖ ≤ q * (‖rr k‖ + δ) :=
        mul_le_mul_of_nonneg_left h3 hq0
      have h5 : q * (‖rr k‖ + δ) ≤ q * (q ^ k * ‖y‖ + k * δ + δ) := by nlinarith
      have h6 : q * (q ^ k * ‖y‖ + k * δ + δ) ≤ q ^ (k + 1) * ‖y‖ + (k + 1) * δ := by
        have hqk : 0 ≤ q ^ k := pow_nonneg hq0 k
        have hy : 0 ≤ ‖y‖ := norm_nonneg y
        have hkd : 0 ≤ (k : ℝ) * δ := by positivity
        have hmul : q * (q ^ k * ‖y‖) = q ^ (k + 1) * ‖y‖ := by ring
        nlinarith [hq1.le, hδ.le]
      push_cast
      push_cast at h5 h6
      linarith
  have hmain : ∀ m : ℕ,
      ‖(H (S m) + B (S m) - lam • (S m : F)) - (y - rr m)‖ ≤ m * δ := by
    intro m
    induction m with
    | zero => simp [hSdef, hrr0]
    | succ m ih =>
      have hSsucc : S (m + 1) = S m + v m := by
        simp [hSdef, Finset.sum_range_succ]
      have hdiff : (H (S (m + 1)) + B (S (m + 1)) - lam • ((S (m + 1) : D) : F))
            - (y - rr (m + 1))
          = ((H (S m) + B (S m) - lam • (S m : F)) - (y - rr m))
            + ((H (v m) - lam • (v m : F)) - rr m) := by
        simp only [hSsucc, hrrs m, map_add, Submodule.coe_add]
        module
      rw [hdiff]
      calc ‖((H (S m) + B (S m) - lam • (S m : F)) - (y - rr m))
              + ((H (v m) - lam • (v m : F)) - rr m)‖
          ≤ ‖(H (S m) + B (S m) - lam • (S m : F)) - (y - rr m)‖
            + ‖(H (v m) - lam • (v m : F)) - rr m‖ := norm_add_le _ _
        _ ≤ m * δ + δ := by
            have := hpick (rr m)
            simp only [hvdef]
            linarith [ih]
        _ = (m + 1 : ℕ) * δ := by push_cast; ring
  refine ⟨H (S n) + B (S n) - lam • (S n : F), ?_, ⟨S n, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hsplit : (H (S n) + B (S n) - lam • (S n : F)) - y
      = ((H (S n) + B (S n) - lam • (S n : F)) - (y - rr n)) - rr n := by abel
  have hfin : 2 * (n : ℝ) * δ ≤ r / 2 := by
    have heq : 2 * ((n : ℝ) + 1) * δ = r / 2 := by
      rw [hδdef]; field_simp; ring
    nlinarith [hδ.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖(H (S n) + B (S n) - lam • (S n : F)) - y‖
      = ‖((H (S n) + B (S n) - lam • (S n : F)) - (y - rr n)) - rr n‖ := by rw [hsplit]
    _ ≤ ‖(H (S n) + B (S n) - lam • (S n : F)) - (y - rr n)‖ + ‖rr n‖ := norm_sub_le _ _
    _ ≤ n * δ + (q ^ n * ‖y‖ + n * δ) := add_le_add (hmain n) (hrrbound n)
    _ < r := by linarith

theorem essentiallySelfAdjointOn_add_relBounded [CompleteSpace F] (H B : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (hB : SymmetricOn D B)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) :
    EssentiallySelfAdjointOn D (H + B) := by
  set K : D →ₗ[ℂ] F := H + B with hK
  have hKapply : ∀ x : D, K x = H x + B x := fun x => rfl
  have hKsymm : SymmetricOn D K := symmetricOn_add hH hB
  -- `H` has trivial deficiency spaces at every non-real point
  have hHall : ∀ σ : ℂ, σ.im ≠ 0 → DeficiencyTrivialAt D H σ := by
    intro σ hσ
    refine deficiencyTrivialAt_of_dense_range H hH 1 one_ne_zero σ hσ ?_ ?_
    · have := dense_range_of_deficiencyTrivialAt H ((1 : ℝ) * Complex.I) (by simpa using hesa.2)
      simpa using this
    · simpa using hesa.1
  -- a shift large enough to make the contraction factor `< 1`
  set e : ℝ := (b + 1) / (1 - a) with hedef
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have he0' : (0 : ℝ) < e := by rw [hedef]; positivity
  have he0 : e ≠ 0 := ne_of_gt he0'
  have habse : |e| = e := abs_of_pos he0'
  have hqlt : ∀ d : ℝ, e ≤ |d| → a + b / |d| < 1 := by
    intro d hd
    have hd0 : (0 : ℝ) < |d| := lt_of_lt_of_le he0' hd
    have hbe : b / |d| ≤ b / e := by
      rcases eq_or_lt_of_le hb with h | h
      · simp [← h]
      · exact div_le_div_of_nonneg_left hb he0' hd
    have hlt : b / e < 1 - a := by
      rw [hedef, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdenseH : ∀ d : ℝ, d ≠ 0 →
      Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) := by
    intro d hd
    refine dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (hHall _ ?_)
    simp [hd]
  have hdenseK : ∀ d : ℝ, e ≤ |d| →
      Dense (Set.range fun x : D => (H x + B x) - ((d : ℂ) * Complex.I) • (x : F)) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      intro h
      rw [h] at hd
      simp at hd
      linarith
    exact dense_range_add_relBounded H B hH ha hb hd0 hrel (hqlt d hd) (hdenseH d hd0)
  have hself : e ≤ |e| := le_of_eq habse.symm
  have hneg : e ≤ |(-e)| := by rw [abs_neg]; exact hself
  have hdefK : DeficiencyTrivialAt D K ((e : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_dense K _ ?_
    have hconj : (starRingEnd ℂ) ((e : ℂ) * Complex.I) = ((-e : ℝ) : ℂ) * Complex.I := by
      push_cast
      simp [mul_comm]
    rw [hconj]
    simpa [hKapply] using hdenseK (-e) hneg
  have hdenseKe : Dense (Set.range fun x : D => K x - ((e : ℂ) * Complex.I) • (x : F)) := by
    simpa [hKapply] using hdenseK e hself
  exact ⟨deficiencyTrivialAt_of_dense_range K hKsymm e he0 Complex.I (by simp) hdenseKe hdefK,
    deficiencyTrivialAt_of_dense_range K hKsymm e he0 (-Complex.I) (by simp) hdenseKe hdefK⟩
end BookProof.KatoRellich
namespace BookProof.HyperbolicQuadratic
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
theorem deficiencyTrivialAt_of_diagonal (v : ι → E) (lam : ι → ℝ)
    (htot : ∀ w : E, (∀ i, (inner ℂ (v i) w : ℂ) = 0) → w = 0)
    {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) (hmem : ∀ i, v i ∈ D)
    (hT : ∀ (i : ι) (h : v i ∈ D), T ⟨v i, h⟩ = ((lam i : ℝ) : ℂ) • v i)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  refine htot w fun i => ?_
  have h := hw ⟨v i, hmem i⟩
  rw [hT i (hmem i), inner_smul_left, Complex.conj_ofReal] at h
  have hne : ((lam i : ℝ) : ℂ) - z ≠ 0 := by
    intro hc
    have hzi : z = ((lam i : ℝ) : ℂ) := by linear_combination -hc
    rw [hzi] at hz
    simp at hz
  have hprod : (((lam i : ℝ) : ℂ) - z) * (inner ℂ (v i) w : ℂ) = 0 := by linear_combination h
  exact (mul_eq_zero.mp hprod).resolve_left hne

theorem hermiteMvLp_total (w : L2d d) (h : ∀ a, (inner ℂ (hermiteMvLp a) w : ℂ) = 0) :
    w = 0 := by
  have hrepr : (hermiteMvBasis (d := d)).repr w = 0 := by
    ext a
    rw [HilbertBasis.repr_apply_apply, hermiteMvBasis_apply, h a]
    simp
  simpa using congrArg (hermiteMvBasis (d := d)).repr.symm hrepr

theorem quadOp_deficiencyTrivialAt (c : Fin d → ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (quadOp c) z :=
  deficiencyTrivialAt_of_diagonal hermiteMvLp (quadSymbol c) hermiteMvLp_total (quadOp c)
    hermiteMvLp_mem_core (fun a h => quadOp_hermiteMvLp c a h) hz

theorem quadOp_essentiallySelfAdjoint (c : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOp c) :=
  ⟨quadOp_deficiencyTrivialAt c (by simp), quadOp_deficiencyTrivialAt c (by simp)⟩
end BookProof.HyperbolicQuadratic
namespace BookProof.HermiteRelative
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} {d : ℕ}
theorem quadOp_add_firstOrder_essentiallySelfAdjoint (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hc : ∀ i, c0 ≤ c i) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOp c + foOp b b') := by
  classical
  set K : ℝ := ∑ i, (|b i| + |b' i|) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => by positivity
  set e : ℝ := 1 / (2 * (K + 1)) with he
  have he0 : 0 < e := by
    have : 0 < 2 * (K + 1) := by linarith
    positivity
  refine BookProof.KatoRellich.essentiallySelfAdjointOn_add_relBounded _ _ (quadOp_symmetric c)
    (quadOp_essentiallySelfAdjoint c) (foOp_symmetric b b') (a := K * e)
    (b := K * (2 / (c0 * e))) (by positivity) ?_ (by positivity) ?_
  · rw [he]
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  · intro u
    have h := norm_foOp_le c hc0 hc b b' he0 u
    calc ‖foOp b b' u‖ ≤ K * (e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖) := h
      _ = K * e * ‖quadOp c u‖ + K * (2 / (c0 * e)) * ‖(u : L2d d)‖ := by ring

theorem harmonicOsc_add_linearPotential_essentiallySelfAdjoint (b : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOp (fun _ => (1 : ℝ)) + foOp b 0) :=
  quadOp_add_firstOrder_essentiallySelfAdjoint _ (c0 := 1) one_pos (fun _ => le_rfl) b 0
end
end BookProof.HermiteRelative

open BookProof.HermiteRelative
open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
variable {d : ℕ}

theorem solution (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hc : ∀ i, c0 ≤ c i) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOp c + foOp b b') := by
  exact BookProof.HermiteRelative.quadOp_add_firstOrder_essentiallySelfAdjoint c hc0 hc b b'
#print axioms solution
