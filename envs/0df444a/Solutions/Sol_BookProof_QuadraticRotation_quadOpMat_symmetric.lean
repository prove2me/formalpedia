-- Prove2me | solution 1 for BookProof.QuadraticRotation.quadOpMat_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:56.333558+00:00
-- url     : https://prove2.me/submissions/27e95666-7e7e-4ff2-8a9e-aa1997d3cb4d

import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

/-- Complex conjugation of coefficients. -/
abbrev qrSP {d : ℕ} (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ :=
  MvPolynomial.map (starRingEnd ℂ) p

theorem qr_conj_eval {d : ℕ} (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (qrSP p) := by
  rw [qrSP, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  simp

theorem qr_inner {d : ℕ} (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (qrSP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx]
  simp only [pgFun, map_mul, Complex.conj_ofReal, qr_conj_eval, gaussWD_eq_sq]
  push_cast
  ring

/-- Gauss adjointness of two polynomial operators. -/
def QrAdj {d : ℕ} (S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ p q, gaussInt (qrSP (S p) * q) = gaussInt (qrSP p * T q)

theorem qr_gaussInt_zero {d : ℕ} : gaussInt (0 : MvPolynomial (Fin d) ℂ) = 0 := by
  have h := gaussInt_smul (0 : ℂ) (0 : MvPolynomial (Fin d) ℂ)
  simpa using h

theorem qr_gaussInt_sub {d : ℕ} (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h := gaussInt_add (r - s) s
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem qrAdj_add {d : ℕ} {S S' T T' : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (h1 : QrAdj S S') (h2 : QrAdj T T') : QrAdj (S + T) (S' + T') := by
  intro p q
  simp only [LinearMap.add_apply, map_add, add_mul, mul_add, gaussInt_add, h1 p q, h2 p q]

theorem qrAdj_smul {d : ℕ} {S S' : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (c : ℂ) (hc : starRingEnd ℂ c = c) (h : QrAdj S S') : QrAdj (c • S) (c • S') := by
  intro p q
  simp only [LinearMap.smul_apply, MvPolynomial.smul_eq_C_mul, qrSP, map_mul, map_C,
    RingHom.coe_comp, Function.comp_apply, hc]
  rw [show ∀ a b : MvPolynomial (Fin d) ℂ, C c * a * b = c • (a * b) from
      fun a b => by rw [MvPolynomial.smul_eq_C_mul]; ring,
    show ∀ a b : MvPolynomial (Fin d) ℂ, a * (C c * b) = c • (a * b) from
      fun a b => by rw [MvPolynomial.smul_eq_C_mul]; ring,
    gaussInt_smul, gaussInt_smul, h p q]

theorem qrAdj_zero {d : ℕ} : QrAdj (0 : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) 0 := by
  intro p q
  simp [qr_gaussInt_zero]

theorem qrAdj_sum {d : ℕ} {ι : Type*} (s : Finset ι)
    {S S' : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (h : ∀ i, QrAdj (S i) (S' i)) : QrAdj (∑ i ∈ s, S i) (∑ i ∈ s, S' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using qrAdj_zero
  | insert v s hv ih =>
      rw [Finset.sum_insert hv, Finset.sum_insert hv]
      exact qrAdj_add (h v) ih

theorem qrAdj_comp {d : ℕ} {S S' T T' : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (h1 : QrAdj S S') (h2 : QrAdj T T') : QrAdj (S.comp T) (T'.comp S') := by
  intro p q
  simp only [LinearMap.comp_apply]
  rw [h1, h2]

theorem qrAdj_mulX {d : ℕ} (i : Fin d) : QrAdj (mulXPoly i) (mulXPoly i) := by
  intro p q
  simp only [mulXPoly, LinearMap.coe_mk, AddHom.coe_mk, qrSP, map_mul, map_X]
  congr 1
  ring

theorem qrAdj_mom {d : ℕ} (j : Fin d) : QrAdj (momPoly j) (momPoly j) := by
  intro p q
  set a := qrSP p with ha
  have hst : qrSP (momPoly j p)
      = C Complex.I * (pderiv j a - C (1 / 2 : ℂ) * (X j * a)) := by
    simp only [momPoly, LinearMap.coe_mk, AddHom.coe_mk, ha, qrSP]
    simp only [map_mul, map_sub, map_C, map_X, pderiv_map, map_neg, Complex.conj_I, neg_neg,
      map_div₀, map_one, map_ofNat]
  have hR : qrSP p * momPoly j q
      = C (-Complex.I) * (a * pderiv j q - C (1 / 2 : ℂ) * (X j * (a * q))) := by
    simp only [momPoly, LinearMap.coe_mk, AddHom.coe_mk, ← ha]
    ring
  have hdiff : C Complex.I * (pderiv j a - C (1 / 2 : ℂ) * (X j * a)) * q
      = C (-Complex.I) * (a * pderiv j q - C (1 / 2 : ℂ) * (X j * (a * q)))
        + C Complex.I * (pderiv j (a * q) - X j * (a * q)) := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_neg]
    have h2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
      rw [← map_ofNat C 2, ← map_mul]; norm_num
    linear_combination (-(C Complex.I * X j * a * q)) * h2
  rw [hst, hR, hdiff, gaussInt_add, ← MvPolynomial.smul_eq_C_mul (a := Complex.I),
    gaussInt_smul Complex.I, qr_gaussInt_sub, gaussInt_pderiv, sub_self, mul_zero, add_zero]

variable {d : ℕ}
theorem solution {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    SymmetricOn (polyGaussCore (d := d)) (quadOpMat A) := by
  have hsym : ∀ k l, A l k = A k l := fun k l => by
    have := congrFun (congrFun hA k) l
    simpa [Matrix.conjTranspose_apply] using this
  have hadj : QrAdj (quadPolyMat A) (quadPolyMat A) := by
    have h0 : QrAdj (quadPolyMat A)
        (∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
          ((momPoly l).comp (momPoly k) + (1/4 : ℂ) • ((mulXPoly l).comp (mulXPoly k)))) := by
      unfold quadPolyMat
      refine qrAdj_sum _ fun k => qrAdj_sum _ fun l => ?_
      refine qrAdj_smul _ (Complex.conj_ofReal _) (qrAdj_add (qrAdj_comp (qrAdj_mom k)
        (qrAdj_mom l)) (qrAdj_smul _ ?_ (qrAdj_comp (qrAdj_mulX k) (qrAdj_mulX l))))
      norm_num [map_div₀]
      rw [show (starRingEnd ℂ) 4 = 4 from map_ofNat _ 4]
      norm_num
    have heq : (∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
          ((momPoly l).comp (momPoly k) + (1/4 : ℂ) • ((mulXPoly l).comp (mulXPoly k))))
        = quadPolyMat A := by
      unfold quadPolyMat
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hsym]
    rw [heq] at h0
    exact h0
  intro x y
  obtain ⟨p, rfl⟩ := (coreEquiv (d := d)).surjective x
  obtain ⟨q, rfl⟩ := (coreEquiv (d := d)).surjective y
  have hc : ∀ r, ((coreEquiv (d := d) r : polyGaussCore (d := d)) : L2d d) = pgLp r :=
    fun r => rfl
  have hq : ∀ r, quadOpMat A (coreEquiv (d := d) r) = pgLp (quadPolyMat A r) := by
    intro r
    simp [quadOpMat, coreOp, LinearEquiv.symm_apply_apply]
    rfl
  rw [hq, hq, hc, hc, qr_inner, qr_inner]
  exact hadj p q
