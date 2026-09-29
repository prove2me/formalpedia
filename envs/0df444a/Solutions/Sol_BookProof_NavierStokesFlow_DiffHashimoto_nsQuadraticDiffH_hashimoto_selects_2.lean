-- Prove2me | solution 2 for BookProof.NavierStokesFlow.DiffHashimoto.nsQuadraticDiffH_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T20:07:16.177153+00:00
-- url     : https://prove2.me/submissions/83a442ad-bc19-4e1b-8054-e47d4d28e323

import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterNavierStokesSignedShift
import Definitions.Def_ChapterNavierStokesDiffHashimoto
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHashimotoComplexShifts
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_esa_of_farisLavine
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

set_option maxHeartbeats 4000000
namespace BookProof.NavierStokesFlow.DiffHashimoto
open Filter Topology MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative BookProof.NavierStokesFlow.DifferentialL2
noncomputable section
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem polySym_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (hT : ∀ i ∈ s, BookProof.YangMillsHermite.PolySym (T i)) :
    BookProof.YangMillsHermite.PolySym (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro p q
      simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hT i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem polySym_id {d : ℕ} :
    BookProof.YangMillsHermite.PolySym (LinearMap.id (R := ℂ) (M := MvPolynomial (Fin d) ℂ)) :=
  fun _ _ => rfl

theorem fieldPoly_polySym (i : Fin 3) :
    BookProof.YangMillsHermite.PolySym (fieldPoly A c i) :=
  (polySym_sum _ _ fun k _ => (polySym_mulXPoly (d := 3) k).real_smul).add
    (polySym_id.real_smul)

theorem coreOp_id {d : ℕ} :
    coreOp (LinearMap.id (R := ℂ) (M := MvPolynomial (Fin d) ℂ))
      = LinearMap.id (R := ℂ) (M := (polyGaussCore (d := d))) := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := d)).surjective y
  simp [coreOp_coreEquiv]

theorem coreOp_fieldPoly (i : Fin 3) : coreOp (fieldPoly A c i) = fieldOp A c i := by
  rw [fieldPoly, fieldOp, coreOp_add, coreOp_smul, coreOp_id, coreOp_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [coreOp_smul, posOp]

theorem nsDiffPoly_polySym : BookProof.YangMillsHermite.PolySym (nsDiffPoly A c) :=
  polySym_sum _ _ fun i _ =>
    BookProof.YangMillsHermite.weylProd_polySym (polySym_momPoly (d := 3) i)
      (fieldPoly_polySym A c i)

theorem half_cast : (((1 / 2 : ℝ) : ℂ)) = (1 : ℂ) / 2 := by norm_num

theorem nsDiffH_eq_coreOp : coreOp (nsDiffPoly A c) = nsDiffH A c := by
  rw [nsDiffPoly, nsDiffH, coreOp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BookProof.YangMillsHermite.weylProd, coreOp_smul, coreOp_add, coreOp_comp, coreOp_comp,
    coreOp_fieldPoly, half_cast]
  rfl

theorem nsDiffH_symmetricOn :
    SymmetricOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by
  have h := symmetricOn_of_polySym (nsDiffPoly_polySym A c)
  rwa [nsDiffH_eq_coreOp] at h
end
end BookProof.NavierStokesFlow.DiffHashimoto

namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}








section Complete
variable [CompleteSpace F]



end Complete
end BookProof.HashimotoShiftInvert
namespace BookProof.ChapterH9
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem norm_sub_starProjection_le (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (u w : E) (hw : w ∈ K) : ‖u - K.starProjection u‖ ≤ ‖u - w‖ := by
  rw [Submodule.starProjection_minimal]
  refine ciInf_le_of_le ⟨0, ?_⟩ (⟨w, hw⟩ : K) le_rfl
  rintro r ⟨x, rfl⟩
  positivity

end BookProof.ChapterH9
namespace BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem starProjection_tendsto_of_monotone_dense (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (hmono : Monotone K)
    (hdense : Dense ((⨆ n : ℕ, K n : Submodule ℂ F) : Set F)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨w, hw, hwd⟩ := hdense.exists_dist_lt u heps
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hw
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖u - (K n).starProjection u‖ ≤ ‖u - w‖ :=
    BookProof.ChapterH9.norm_sub_starProjection_le _ u w (hmono hn hN)
  have h2 : ‖u - w‖ < eps := by simpa [dist_eq_norm] using hwd
  have h3 : ‖(K n).starProjection u - u‖ = ‖u - (K n).starProjection u‖ := norm_sub_rev _ _
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), h3]
  exact lt_of_le_of_lt h1 h2

theorem compression_tendsto_of_starProjection_tendsto (K : ℕ → Submodule ℂ F)
    [∀ n, (K n).HasOrthogonalProjection] (A : F →L[ℂ] F)
    (hP : ∀ u : F, Tendsto (fun n : ℕ => (K n).starProjection u) atTop (nhds u)) (u : F) :
    Tendsto (fun n : ℕ => (K n).starProjection (A ((K n).starProjection u)))
      atTop (nhds (A u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ, ‖(K n).starProjection (A ((K n).starProjection u)) - A u‖
      ≤ ‖A‖ * ‖(K n).starProjection u - u‖ + ‖(K n).starProjection (A u) - A u‖ := by
    intro n
    have hsplit : (K n).starProjection (A ((K n).starProjection u)) - A u
        = (K n).starProjection (A ((K n).starProjection u) - A u)
          + ((K n).starProjection (A u) - A u) := by
      simp only [map_sub]
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    gcongr
    refine le_trans ((K n).norm_starProjection_apply_le _) ?_
    have hAsub : A ((K n).starProjection u) - A u = A ((K n).starProjection u - u) := by
      rw [map_sub]
    rw [hAsub]
    exact A.le_opNorm _
  have h1 : Tendsto (fun n : ℕ => ‖A‖ * ‖(K n).starProjection u - u‖) atTop (nhds 0) := by
    have := hP u
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this.const_mul ‖A‖
  have h2 : Tendsto (fun n : ℕ => ‖(K n).starProjection (A u) - A u‖) atTop (nhds 0) := by
    have := hP (A u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa using h1.add h2)

theorem galerkinSpan_mono (b : HilbertBasis ℕ ℂ F) {m n : ℕ} (hmn : m ≤ n) :
    galerkinSpan b m ≤ galerkinSpan b n :=
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi hmn)

theorem basis_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : i < m) :
    b i ∈ galerkinSpan b m :=
  Submodule.subset_span ⟨i, him, rfl⟩


theorem galerkinSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ≤ finiteModeDomain b :=
  Submodule.span_mono (by rintro x ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)

theorem finiteModeDomain_eq_iSup (b : HilbertBasis ℕ ℂ F) :
    finiteModeDomain b = ⨆ m : ℕ, galerkinSpan b m := by
  refine le_antisymm ?_ (iSup_le fun m => galerkinSpan_le_finiteModeDomain b m)
  rw [finiteModeDomain, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (i + 1) (basis_mem_galerkinSpan b (Nat.lt_succ_self i))


theorem finiteModeDomain_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((finiteModeDomain b : Submodule ℂ F) : Set F) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

theorem galerkinSpan_iSup_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((⨆ m : ℕ, galerkinSpan b m : Submodule ℂ F) : Set F) := by
  rw [← finiteModeDomain_eq_iSup]
  exact finiteModeDomain_dense b

theorem galerkinProj_tendsto (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => (galerkinSpan b m).starProjection u) atTop (nhds u) :=
  starProjection_tendsto_of_monotone_dense _ (fun _ _ h => galerkinSpan_mono b h)
    (galerkinSpan_iSup_dense b) u

@[simp] theorem galerkinCompression_apply (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    (u : F) : galerkinCompression A b m u
      = (galerkinSpan b m).starProjection (A ((galerkinSpan b m).starProjection u)) := rfl

theorem galerkinCompression_tendsto (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => galerkinCompression A b m u) atTop (nhds (A u)) :=
  compression_tendsto_of_starProjection_tendsto _ A (galerkinProj_tendsto b) u
end BookProof.HermiteGalerkin

namespace BookProof.HermiteGalerkin
open Filter Topology
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]







end BookProof.HermiteGalerkin

namespace BookProof.HashimotoShiftInvert
open Filter Topology
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HermiteGalerkin
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}






end BookProof.HashimotoShiftInvert

namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
theorem IsShiftInvertC.mem {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) : X u ∈ Dom := (h.2 u).choose

theorem IsShiftInvertC.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    γ • X u - A ⟨X u, h.mem u⟩ = u := (h.2 u).choose_spec

theorem IsShiftInvertC.apply_eq {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    A ⟨X u, h.mem u⟩ = γ • X u - u := by
  have h1 : γ • X u - A ⟨X u, h.mem u⟩ = u := h.shift_apply u
  have ha : γ • X u = u + A ⟨X u, h.mem u⟩ := sub_eq_iff_eq_add.mp h1
  rw [ha]; abel

theorem IsShiftInvertC.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (u : F) :
    ‖X u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hb : |γ.im| * ‖((⟨X u, h.mem u⟩ : Dom) : F)‖ ≤ ‖cshiftMap A γ ⟨X u, h.mem u⟩‖ :=
    norm_cshiftMap_ge hsym _ _
  rw [show cshiftMap A γ ⟨X u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  simpa using hb

theorem IsShiftInvertC.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    ‖X‖ ≤ |γ.im|⁻¹ :=
  X.opNorm_le_bound (by positivity) (h.norm_apply_le hsym hγ)

theorem IsShiftInvertC.injective {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) : Function.Injective X := by
  intro u v huv
  have hu := h.shift_apply u
  have hv := h.shift_apply v
  have hsub : (⟨X u, h.mem u⟩ : Dom) = ⟨X v, h.mem v⟩ := Subtype.ext huv
  rw [← hu, ← hv, hsub, huv]

theorem IsShiftInvertC.dom_eq_range {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) : Dom = LinearMap.range (X : F →ₗ[ℂ] F) := by
  apply le_antisymm
  · intro x hx
    exact ⟨cshiftMap A γ ⟨x, hx⟩, h.1 ⟨x, hx⟩⟩
  · rintro _ ⟨u, rfl⟩
    exact h.mem u


theorem shiftInvertC_determines {Dom₁ Dom₂ : Submodule ℂ F} {A₁ : Dom₁ →ₗ[ℂ] F}
    {A₂ : Dom₂ →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h₁ : IsShiftInvertC A₁ γ X) (h₂ : IsShiftInvertC A₂ γ X) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (hx₁ : x ∈ Dom₁) (hx₂ : x ∈ Dom₂), A₁ ⟨x, hx₁⟩ = A₂ ⟨x, hx₂⟩ := by
  refine ⟨by rw [h₁.dom_eq_range, h₂.dom_eq_range], ?_⟩
  intro x hx₁ hx₂
  set u : F := cshiftMap A₁ γ ⟨x, hx₁⟩ with hu
  have hXu : X u = x := h₁.1 ⟨x, hx₁⟩
  have e₁ : A₁ ⟨X u, h₁.mem u⟩ = γ • X u - u := h₁.apply_eq u
  have e₂ : A₂ ⟨X u, h₂.mem u⟩ = γ • X u - u := h₂.apply_eq u
  have c₁ : (⟨X u, h₁.mem u⟩ : Dom₁) = ⟨x, hx₁⟩ := Subtype.ext hXu
  have c₂ : (⟨X u, h₂.mem u⟩ : Dom₂) = ⟨x, hx₂⟩ := Subtype.ext hXu
  rw [c₁] at e₁
  rw [c₂] at e₂
  rw [e₁, e₂]

theorem isShiftInvertC_unique {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A γ Y) : X = Y := by
  ext u
  have h1 : Y (cshiftMap A γ ⟨X u, hX.mem u⟩) = X u := hY.1 ⟨X u, hX.mem u⟩
  rw [show cshiftMap A γ ⟨X u, hX.mem u⟩ = u from hX.shift_apply u] at h1
  exact h1.symm

theorem isShiftInvertC_of_rightInverse {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (hright : ∀ u : F, ∃ h : X u ∈ Dom, cshiftMap A γ ⟨X u, h⟩ = u) :
    IsShiftInvertC A γ X := by
  refine ⟨fun x => ?_, hright⟩
  obtain ⟨hmem, hval⟩ := hright (cshiftMap A γ x)
  have heq : (⟨X (cshiftMap A γ x), hmem⟩ : Dom) = x :=
    cshiftMap_injective hsym hγ (by rw [hval])
  exact congrArg Subtype.val heq

theorem exists_isShiftInvertC {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    {γ : ℂ} (hγ : γ.im ≠ 0) (hsurj : Function.Surjective (cshiftMap A γ)) :
    ∃ X : F →L[ℂ] F, IsShiftInvertC A γ X := by
  classical
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hinj : Function.Injective (cshiftMap A γ) := cshiftMap_injective hsym hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (cshiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : cshiftMap A γ (g (u + v)) = cshiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : cshiftMap A γ (g (c • u)) = cshiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
    intro u
    have hb : |γ.im| * ‖((g u : Dom) : F)‖ ≤ ‖cshiftMap A γ (g u)‖ := norm_cshiftMap_ge hsym _ _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hb
  refine ⟨L.mkContinuous |γ.im|⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (cshiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change cshiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]


theorem shiftInvertC_resolvent_identity {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) (u : F) :
    X u - Y u = (δ - γ) • X (Y u) := by
  have hy : δ • Y u - A ⟨Y u, hY.mem u⟩ = u := hY.shift_apply u
  have hsplit : cshiftMap A γ ⟨Y u, hY.mem u⟩ + (δ - γ) • Y u = u := by
    rw [cshiftMap_apply]
    have hrw : γ • ((⟨Y u, hY.mem u⟩ : Dom) : F) - A ⟨Y u, hY.mem u⟩ + (δ - γ) • Y u
        = δ • Y u - A ⟨Y u, hY.mem u⟩ := by
      module
    rw [hrw, hy]
  have hXu : X u = Y u + (δ - γ) • X (Y u) := by
    conv_lhs => rw [← hsplit]
    rw [map_add, map_smul, hX.1 ⟨Y u, hY.mem u⟩]
  rw [hXu]; abel

theorem shiftInvertC_commute {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) : X ∘L Y = Y ∘L X := by
  rcases eq_or_ne γ δ with rfl | hne
  · rw [isShiftInvertC_unique hX hY]
  · have h1 : ∀ u, X u - Y u = (δ - γ) • X (Y u) :=
      shiftInvertC_resolvent_identity hX hY
    have h2 : ∀ u, Y u - X u = (γ - δ) • Y (X u) :=
      shiftInvertC_resolvent_identity hY hX
    have hd : (δ - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    ext u
    have h3 : (δ - γ) • X (Y u) = (δ - γ) • Y (X u) := by
      have hneg : (δ - γ) • X (Y u) = -((γ - δ) • Y (X u)) := by
        rw [← h1 u, ← h2 u]; abel
      rw [hneg]; module
    exact smul_right_injective F hd h3

theorem shiftInvertC_comp_one_sub {A : Dom →ₗ[ℂ] F} {γ δ : ℂ} {X Y : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hY : IsShiftInvertC A δ Y) :
    X ∘L (ContinuousLinearMap.id ℂ F - (δ - γ) • Y) = Y := by
  ext u
  have h := shiftInvertC_resolvent_identity hX hY u
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sub, map_smul]
  rw [← h]
  abel

@[simp] theorem rkVec_zero (X : ℕ → F →L[ℂ] F) (v : F) : rkVec X v 0 = v := rfl

@[simp] theorem rkVec_succ (X : ℕ → F →L[ℂ] F) (v : F) (k : ℕ) :
    rkVec X v (k + 1) = X k (rkVec X v k) := rfl


@[simp] theorem sirkDen_zero (Xm : F →L[ℂ] F) (c : ℕ → ℂ) :
    sirkDen Xm c 0 = ContinuousLinearMap.id ℂ F := rfl

@[simp] theorem sirkDen_succ (Xm : F →L[ℂ] F) (c : ℕ → ℂ) (k : ℕ) :
    sirkDen Xm c (k + 1) = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k := rfl

theorem sirkDen_commute {Xm T : F →L[ℂ] F} (c : ℕ → ℂ) (hT : T ∘L Xm = Xm ∘L T) (k : ℕ) :
    T ∘L sirkDen Xm c k = sirkDen Xm c k ∘L T := by
  induction k with
  | zero => ext u; simp
  | succ k ih =>
      have h1 : T ∘L (ContinuousLinearMap.id ℂ F - c k • Xm)
          = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L T := by
        ext u
        have := congrArg (fun S : F →L[ℂ] F => S u) hT
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sub, map_smul, this]
      calc T ∘L ((ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k)
          = (T ∘L (ContinuousLinearMap.id ℂ F - c k • Xm)) ∘L sirkDen Xm c k := rfl
        _ = ((ContinuousLinearMap.id ℂ F - c k • Xm) ∘L T) ∘L sirkDen Xm c k := by rw [h1]
        _ = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L (T ∘L sirkDen Xm c k) := rfl
        _ = (ContinuousLinearMap.id ℂ F - c k • Xm) ∘L (sirkDen Xm c k ∘L T) := by rw [ih]
        _ = ((ContinuousLinearMap.id ℂ F - c k • Xm) ∘L sirkDen Xm c k) ∘L T := rfl

theorem sirkDen_rkVec {A : Dom →ₗ[ℂ] F} {γ : ℕ → ℂ} {X : ℕ → F →L[ℂ] F} (m : ℕ)
    (hX : ∀ j, IsShiftInvertC A (γ j) (X j)) (v : F) (k : ℕ) :
    sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hcomm : X k ∘L X m = X m ∘L X k :=
        shiftInvertC_commute (hX k) (hX m)
      have hden : X k ∘L sirkDen (X m) (fun i => γ m - γ i) k
          = sirkDen (X m) (fun i => γ m - γ i) k ∘L X k :=
        sirkDen_commute _ hcomm k
      have hkey : (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) ∘L X k = X m := by
        have h := shiftInvertC_comp_one_sub (hX k) (hX m)
        have hcomm' : X k ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m)
            = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) ∘L X k := by
          ext u
          have := congrArg (fun S : F →L[ℂ] F => S u) hcomm
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
            ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.coe_smul', Pi.smul_apply, map_sub, map_smul, this]
        rw [← hcomm', h]
      calc sirkDen (X m) (fun i => γ m - γ i) (k + 1) (rkVec X v (k + 1))
          = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m)
              (sirkDen (X m) (fun i => γ m - γ i) k (X k (rkVec X v k))) := rfl
        _ = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m)
              (X k (sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k))) := by
              have := congrArg (fun S : F →L[ℂ] F => S (rkVec X v k)) hden
              simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at this
              rw [← this]
        _ = (ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) (X k ((X m ^ k) v)) := by rw [ih]
        _ = ((ContinuousLinearMap.id ℂ F - (γ m - γ k) • X m) ∘L X k) ((X m ^ k) v) := rfl
        _ = (X m ^ (k + 1)) v := by
              rw [hkey, pow_succ']
              rfl




end BookProof.HashimotoShiftInvert

namespace BookProof.EsaClosure
open Filter Topology
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {D : Submodule ℂ F}
theorem hashimoto_multishift_selects_esa (b : HilbertBasis ℕ ℂ F) (T : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) (hesa : EssentiallySelfAdjointOn D T)
    (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (X : ℕ → F →L[ℂ] F),
      IsSelfAdjointExtension T A ∧
      (∀ j, IsShiftInvertC A (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : F →ₗ[ℂ] F))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ F - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ F) (A' : Dom' →ₗ[ℂ] F), IsShiftInvertC A' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : F) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) := by
  obtain ⟨Dom, A, hA⟩ := exists_isSelfAdjointExtension_of_esa T hdense hsym hesa
  obtain ⟨hext, hsymA, hsa⟩ := hA
  choose X hX using fun j : ℕ =>
    exists_isShiftInvertC hsymA (hγ j) (cshiftMap_surjective hsymA hsa (hγ j))
  refine ⟨Dom, A, X, ⟨hext, hsymA, hsa⟩,
    hX, fun j => (hX j).opNorm_le hsymA (hγ j), fun j => (hX j).dom_eq_range,
    fun j k u => shiftInvertC_resolvent_identity (hX j) (hX k) u,
    fun j k => shiftInvertC_commute (hX j) (hX k),
    fun j m => shiftInvertC_comp_one_sub (hX j) (hX m),
    fun m v k => sirkDen_rkVec m hX v k,
    fun j u => galerkinCompression_tendsto (X j) b u, ?_⟩
  intro j Dom' A' hA'
  obtain ⟨hdom, hval⟩ := shiftInvertC_determines hA' (hX j)
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩
end BookProof.EsaClosure

namespace BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteProductCore
theorem nsDiffH_domain_dense :
    Dense ((polyGaussCore (d := 3) : Submodule ℂ (L2d 3)) : Set (L2d 3)) :=
  polyGaussCore_dense
end BookProof.NavierStokesFlow.DifferentialL2

namespace BookProof.NavierStokesFlow.DiffHashimoto
open Filter Topology MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative BookProof.NavierStokesFlow.DifferentialL2
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem nsDiffH_selfAdjoint_extension :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3),
      IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G :=
  exists_isSelfAdjointExtension_of_esa _ nsDiffH_domain_dense (nsDiffH_symmetricOn A c)
    (BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine A c)

theorem nsDiffH_selfAdjoint_extension_unique {Dom₁ Dom₂ : Submodule ℂ (L2d 3)}
    {G₁ : Dom₁ →ₗ[ℂ] L2d 3} {G₂ : Dom₂ →ₗ[ℂ] L2d 3}
    (h₁ : IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G₁)
    (h₂ : IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G₂) :
    Dom₁ = Dom₂ ∧ ∀ (x : L2d 3) (h : x ∈ Dom₁) (h' : x ∈ Dom₂), G₁ ⟨x, h⟩ = G₂ ⟨x, h'⟩ :=
  isSelfAdjointExtension_unique_of_esa (BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine A c) h₁ h₂

theorem nsDiffH_hashimoto_selects (b : HilbertBasis ℕ ℂ (L2d 3)) (γ : ℕ → ℂ)
    (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : ℕ → L2d 3 →L[ℂ] L2d 3),
      IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2d 3 →ₗ[ℂ] L2d 3))) ∧
      (∀ j k u, X j u - X k u = (γ k - γ j) • X j (X k u)) ∧
      (∀ j k, X j ∘L X k = X k ∘L X j) ∧
      (∀ j m, X j ∘L (ContinuousLinearMap.id ℂ (L2d 3) - (γ m - γ j) • X m) = X m) ∧
      (∀ m v k, sirkDen (X m) (fun i => γ m - γ i) k (rkVec X v k) = (X m ^ k) v) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (L2d 3)) (G' : Dom' →ₗ[ℂ] L2d 3),
        IsShiftInvertC G' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2d 3) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          G' ⟨x, hx'⟩ = G ⟨x, hx⟩) :=
  hashimoto_multishift_selects_esa b _ nsDiffH_domain_dense (nsDiffH_symmetricOn A c)
    (BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine A c) γ hγ

theorem nsDiffH_shiftInvert_selects {γ : ℂ} (hγ : γ.im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : L2d 3 →L[ℂ] L2d 3),
      IsSelfAdjointExtension ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) G ∧
      IsShiftInvertC G γ X ∧
      ‖X‖ ≤ |γ.im|⁻¹ ∧ Dom = LinearMap.range ((X : L2d 3 →ₗ[ℂ] L2d 3)) ∧
      (∀ (Dom' : Submodule ℂ (L2d 3)) (G' : Dom' →ₗ[ℂ] L2d 3), IsShiftInvertC G' γ X →
        Dom' = Dom ∧ ∀ (x : L2d 3) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          G' ⟨x, hx'⟩ = G ⟨x, hx⟩) := by
  obtain ⟨Dom, G, hG⟩ := nsDiffH_selfAdjoint_extension A c
  obtain ⟨hext, hsym, hsa⟩ := hG
  obtain ⟨X, hX⟩ := exists_isShiftInvertC hsym hγ (cshiftMap_surjective hsym hsa hγ)
  refine ⟨Dom, G, X, ⟨hext, hsym, hsa⟩, hX, hX.opNorm_le hsym hγ, hX.dom_eq_range, ?_⟩
  intro Dom' G' hG'
  obtain ⟨hdom, hval⟩ := shiftInvertC_determines hG' hX
  exact ⟨hdom, fun x hx hx' => hval x hx' hx⟩

theorem nsQuadraticDiffH_hashimoto_selects (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ)
    (lap : Fin 3 → ℝ) (b : HilbertBasis ℕ ℂ (L2d 3)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : ℕ → L2d 3 →L[ℂ] L2d 3),
      IsSelfAdjointExtension
        ((polyGaussCore (d := 3)).subtype.comp (nsQuadraticDiffH nu grad lap)) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2d 3 →ₗ[ℂ] L2d 3))) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (L2d 3)) (G' : Dom' →ₗ[ℂ] L2d 3),
        IsShiftInvertC G' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2d 3) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          G' ⟨x, hx'⟩ = G ⟨x, hx⟩) := by
  obtain ⟨Dom, G, X, hext, hsi, hnorm, hdom, _, _, _, _, hgal, hdet⟩ :=
    nsDiffH_hashimoto_selects grad (fun i => -(nu * lap i)) b γ hγ
  exact ⟨Dom, G, X, hext, hsi, hnorm, hdom, hgal, hdet⟩
end BookProof.NavierStokesFlow.DiffHashimoto

open Filter Topology MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.DiffHashimoto
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem solution (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ)
    (lap : Fin 3 → ℝ) (b : HilbertBasis ℕ ℂ (L2d 3)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2d 3)) (G : Dom →ₗ[ℂ] L2d 3) (X : ℕ → L2d 3 →L[ℂ] L2d 3),
      IsSelfAdjointExtension
        ((polyGaussCore (d := 3)).subtype.comp (nsQuadraticDiffH nu grad lap)) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, ‖X j‖ ≤ |(γ j).im|⁻¹) ∧
      (∀ j, Dom = LinearMap.range ((X j : L2d 3 →ₗ[ℂ] L2d 3))) ∧
      (∀ j u, Tendsto (fun n : ℕ => galerkinCompression (X j) b n u) atTop (nhds (X j u))) ∧
      (∀ j (Dom' : Submodule ℂ (L2d 3)) (G' : Dom' →ₗ[ℂ] L2d 3),
        IsShiftInvertC G' (γ j) (X j) →
        Dom' = Dom ∧ ∀ (x : L2d 3) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
          G' ⟨x, hx'⟩ = G ⟨x, hx⟩) := by
  exact BookProof.NavierStokesFlow.DiffHashimoto.nsQuadraticDiffH_hashimoto_selects nu grad lap b γ hγ
#print axioms solution
