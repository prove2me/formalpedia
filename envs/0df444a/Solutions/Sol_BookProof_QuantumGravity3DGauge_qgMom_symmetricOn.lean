-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgMom_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:38:57.129978+00:00
-- url     : https://prove2.me/submissions/652f39f8-109a-4633-8144-371fa46542d4

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge

open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

theorem qgs_conj_eval {d : ℕ} (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p) := by
  rw [starP, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  simp

theorem qgs_inner {d : ℕ} (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx]
  simp only [pgFun, map_mul, Complex.conj_ofReal, qgs_conj_eval, gaussWD_eq_sq]
  push_cast
  ring

theorem qgs_transport {d : ℕ} {D : Submodule ℂ (L2d d)} (Φ : CoreRep d D)
    (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) (hT : PolySym T) :
    SymmetricOn D (D.subtype.comp (Φ.op T)) := by
  intro x y
  obtain ⟨p, rfl⟩ := Φ.equiv.surjective x
  obtain ⟨q, rfl⟩ := Φ.equiv.surjective y
  have h1 : ∀ r, Φ.op T (Φ.equiv r) = Φ.equiv (T r) := by
    intro r; simp [CoreRep.op, LinearEquiv.conj_apply]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, h1, Φ.coe_equiv]
  rw [qgs_inner, qgs_inner]
  exact hT p q

theorem qgs_mul_sym {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (hf : starP f = f) :
    PolySym (mulOp f) := by
  intro p q
  have hf' : MvPolynomial.map (starRingEnd ℂ) f = f := hf
  have : starP (f * p) = f * starP p := by
    simp only [starP, map_mul, hf']
  simp only [mulOp, LinearMap.mulLeft_apply, this]
  congr 1
  ring

theorem qgs_gaussInt_sub {d : ℕ} (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h := gaussInt_add (r - s) s
  rw [sub_add_cancel] at h
  rw [h]; ring

theorem qgs_mom_sym {d : ℕ} (j : Fin d) : PolySym (momOp j) := by
  intro p q
  set a := starP p with ha
  have hst : starP (momOp j p)
      = (Complex.I) • (pderiv j a - ((1 / 2 : ℝ) : ℂ) • (X j * a)) := by
    simp only [momOp, derOp, mulOp, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.mulLeft_apply, Derivation.coeFn_coe, ha, starP]
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_sub, map_C, map_X, pderiv_map,
      map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
  have hR : starP p * momOp j q
      = (-Complex.I) • (a * pderiv j q - ((1 / 2 : ℝ) : ℂ) • (X j * (a * q))) := by
    simp only [momOp, derOp, mulOp, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.mulLeft_apply, Derivation.coeFn_coe, ← ha]
    simp only [MvPolynomial.smul_eq_C_mul, map_neg]
    ring
  have hdiff : (Complex.I) • (pderiv j a - ((1 / 2 : ℝ) : ℂ) • (X j * a)) * q
      = (-Complex.I) • (a * pderiv j q - ((1 / 2 : ℝ) : ℂ) • (X j * (a * q)))
        + Complex.I • (pderiv j (a * q) - X j * (a * q)) := by
    rw [Derivation.leibniz]
    simp only [MvPolynomial.smul_eq_C_mul, smul_eq_mul, map_neg]
    have h2 : (C ((1 / 2 : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
      rw [← map_ofNat C 2, ← map_mul]; simp
    linear_combination (-(C Complex.I * X j * a * q)) * h2
  rw [hst, hR, hdiff, gaussInt_add, gaussInt_smul Complex.I, qgs_gaussInt_sub,
    gaussInt_pderiv, sub_self, mul_zero, add_zero]

variable {D : Submodule ℂ (L2d 84)}
theorem solution (Φ : CoreRep 84 D) (j : Fin 84) :
    SymmetricOn D (D.subtype.comp (qgMom Φ j)) := by
  unfold qgMom
  exact qgs_transport Φ _ (qgs_mom_sym j)
