-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DiffHashimoto.polySym_sum
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:09:00.072542+00:00
-- url     : https://prove2.me/submissions/b776d5ab-e677-426b-bf5d-001c3dc69d0d

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0. https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean
Supporting complete polynomial/core proofs from ChapterYangMillsHermite.lean, ChapterNavierStokesDifferentialL2.lean and ChapterHermiteRelativeBound.lean, same revision. -/
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDiffHashimoto
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

open Filter Topology MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.DiffHashimoto
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
theorem solution {d : ℕ} {ι : Type*} (s : Finset ι)
    (T : ι → Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (hT : ∀ i ∈ s, BookProof.YangMillsHermite.PolySym (T i)) :
    BookProof.YangMillsHermite.PolySym (∑ i ∈ s, T i) := by
  exact BookProof.NavierStokesFlow.DiffHashimoto.polySym_sum s T hT
#print axioms solution
