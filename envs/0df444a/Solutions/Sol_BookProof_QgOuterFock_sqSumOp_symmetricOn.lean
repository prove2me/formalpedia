-- Prove2me | solution 1 for BookProof.QgOuterFock.sqSumOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:23:02.526921+00:00
-- url     : https://prove2.me/submissions/8d309de1-90a1-45c0-bcd0-ddcb3e205707

import Mathlib
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore

set_option autoImplicit false

section C72Helpers

open BookProof.FullQuadratic
open BookProof.HermiteProductCore
open BookProof.QgOuterFock

variable {D : ℕ}

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.Qg3DGaugeEsa
open BookProof.QgHermiteOscillator
open BookProof.DirectSumEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

theorem c72_starP_add (p q : MvPolynomial (Fin D) ℂ) :
    starP (p + q) = starP p + starP q := by
  simp [starP]

theorem c72_starP_sub (p q : MvPolynomial (Fin D) ℂ) :
    starP (p - q) = starP p - starP q := by
  simp [starP]

theorem c72_starP_mul (p q : MvPolynomial (Fin D) ℂ) :
    starP (p * q) = starP p * starP q := by
  simp [starP]

theorem c72_starP_zero : starP (0 : MvPolynomial (Fin D) ℂ) = 0 := by
  simp [starP]

theorem c72_starP_X (j : Fin D) : starP (X j : MvPolynomial (Fin D) ℂ) = X j := by
  simp [starP]

theorem c72_starP_smul (c : ℂ) (p : MvPolynomial (Fin D) ℂ) :
    starP (c • p) = (starRingEnd ℂ c) • starP p := by
  simp [starP, MvPolynomial.smul_eq_C_mul]

theorem c72_starP_pderiv (j : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    starP (pderiv j p) = pderiv j (starP p) := by
  simp [starP, MvPolynomial.pderiv_map]

theorem c72_conj_eval (p : MvPolynomial (Fin D) ℂ) (x : Vd D) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [starP]
  | add p q hp hq => rw [c72_starP_add, map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [c72_starP_mul, map_mul, map_mul, map_mul, hp, c72_starP_X]; simp

theorem c72_inner_pgLp (p q : MvPolynomial (Fin D) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx, pgFun, pgFun, map_mul, Complex.conj_ofReal, c72_conj_eval, map_mul, gaussWD_eq_sq]
  push_cast
  ring

theorem c72_polySym_add {S T : Module.End ℂ (MvPolynomial (Fin D) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (S + T) := by
  intro p q
  rw [LinearMap.add_apply, LinearMap.add_apply, c72_starP_add, add_mul, mul_add,
    gaussInt_add, gaussInt_add, hS, hT]

theorem c72_polySym_rsmul {T : Module.End ℂ (MvPolynomial (Fin D) ℂ)} (r : ℝ)
    (hT : PolySym T) : PolySym (((r : ℝ) : ℂ) • T) := by
  intro p q
  rw [LinearMap.smul_apply, LinearMap.smul_apply, c72_starP_smul, Complex.conj_ofReal,
    smul_mul_assoc, mul_smul_comm, gaussInt_smul, gaussInt_smul, hT]

theorem c72_polySym_zero : PolySym (0 : Module.End ℂ (MvPolynomial (Fin D) ℂ)) := by
  intro p q
  simp [c72_starP_zero]

theorem c72_polySym_sum {ι : Type*} (s : Finset ι)
    (f : ι → Module.End ℂ (MvPolynomial (Fin D) ℂ)) (hf : ∀ i, PolySym (f i)) :
    PolySym (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (c72_polySym_zero (D := D))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact c72_polySym_add (hf a) ih

theorem c72_polySym_comp_self {T : Module.End ℂ (MvPolynomial (Fin D) ℂ)}
    (hT : PolySym T) : PolySym (T.comp T) := by
  intro p q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hT, hT]

theorem c72_polySym_mulOp (f : MvPolynomial (Fin D) ℂ) (hf : starP f = f) :
    PolySym (BookProof.YangMillsHermite.mulOp f) := by
  intro p q
  show gaussInt (starP (f * p) * q) = gaussInt (starP p * (f * q))
  rw [c72_starP_mul, hf]
  congr 1
  ring

theorem c72_starP_linForm (w : Fin D → ℝ) : starP (linForm w) = linForm w := by
  simp [linForm, starP, MvPolynomial.smul_eq_C_mul]

theorem c72_momOp_apply (j : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    BookProof.YangMillsHermite.momOp j p
      = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl

theorem c72_polySym_momOp (j : Fin D) : PolySym (BookProof.YangMillsHermite.momOp j) := by
  intro p q
  rw [c72_momOp_apply, c72_momOp_apply, c72_starP_smul, c72_starP_sub, c72_starP_smul,
    c72_starP_mul, c72_starP_X, c72_starP_pderiv, Complex.conj_ofReal, map_neg, Complex.conj_I,
    neg_neg]
  set r := starP p
  let G : MvPolynomial (Fin D) ℂ →ₗ[ℂ] ℂ :=
    { toFun := gaussInt
      map_add' := gaussInt_add
      map_smul' := fun c s => by rw [gaussInt_smul]; rfl }
  have key := gaussInt_pderiv j (r * q)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at key
  have h0 : G (r * pderiv j q + q * pderiv j r - X j * (r * q)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr key
  change G _ = G _
  rw [← sub_eq_zero, ← map_sub]
  have hpoly : (Complex.I • (pderiv j r - ((1 / 2 : ℝ) : ℂ) • (X j * r))) * q
      - r * ((-Complex.I) • (pderiv j q - ((1 / 2 : ℝ) : ℂ) • (X j * q)))
      = Complex.I • (r * pderiv j q + q * pderiv j r - X j * (r * q)) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_neg]
    have hc : (C (((1 / 2 : ℝ) : ℂ)) : MvPolynomial (Fin D) ℂ) * 2 = 1 := by
      rw [show (2 : MvPolynomial (Fin D) ℂ) = C 2 from rfl, ← C_mul]
      push_cast
      norm_num
    linear_combination (-(C Complex.I * X j * r * q)) * hc
  rw [hpoly, map_smul, h0, smul_zero]

theorem c72_symm_of_polySym (T : Module.End ℂ (MvPolynomial (Fin D) ℂ)) (hT : PolySym T) :
    SymmetricOn (polyGaussCore (d := D)) ((polyGaussCore (d := D)).subtype ∘ₗ coreOp T) := by
  intro x y
  obtain ⟨p, rfl⟩ := (coreEquiv (d := D)).surjective x
  obtain ⟨q, rfl⟩ := (coreEquiv (d := D)).surjective y
  have hc : ∀ s, ((coreEquiv (d := D) s : polyGaussCore (d := D)) : L2d D) = pgLp s :=
    fun s => rfl
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, coreOp, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, hc]
  rw [c72_inner_pgLp, c72_inner_pgLp, hT]

end C72Helpers

open BookProof.FarisLavine BookProof.HermiteProductCore BookProof.QgOuterFock BookProof.NavierStokesFlow.DifferentialL2 BookProof.YangMillsHermite in
theorem solution {D : ℕ} {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    SymmetricOn (polyGaussCore (d := D)) (sqSumOp kappa v) := by
  apply c72_symm_of_polySym
  unfold sqSumPoly
  apply c72_polySym_rsmul
  apply c72_polySym_add
  · apply c72_polySym_sum
    intro j
    apply c72_polySym_rsmul
    exact c72_polySym_comp_self (c72_polySym_momOp j)
  · apply c72_polySym_sum
    intro r
    apply c72_polySym_comp_self
    exact c72_polySym_mulOp _ (c72_starP_linForm _)
