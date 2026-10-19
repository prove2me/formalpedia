-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgCCR
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:45:08.454989+00:00
-- url     : https://prove2.me/submissions/f211475c-fd93-44e6-8b7b-58f117ec57eb

import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgCCR
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {D : Submodule ℂ (L2d 84)}


theorem solution (Φ : CoreRep 84 D) (j k : Fin 84) (x : D) :
    qgCoord Φ j (qgMom Φ k x) - qgMom Φ k (qgCoord Φ j x)
      = (if j = k then Complex.I else 0) • x := by
  unfold qgCoord qgMom CoreRep.op
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  set p := Φ.equiv.symm x with hp
  have hx : x = Φ.equiv p := by simp [hp]
  rw [hx, ← map_sub, ← map_smul]
  congr 1
  simp only [momOp, derOp, mulOp, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.mulLeft_apply, Derivation.leibniz, pderiv_X]
  by_cases h : j = k
  · subst h
    simp [Pi.single_apply, smul_eq_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring
  · simp [Pi.single_apply, h, Ne.symm h, smul_eq_mul]
    simp only [MvPolynomial.smul_eq_C_mul]
    ring

