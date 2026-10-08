-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgCoord_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:20:42.802987+00:00
-- url     : https://prove2.me/submissions/bccaff3a-2123-4f46-8746-2f3055455013

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgCoord_symmetricOn
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.ChapterF7
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}

theorem solution (Φ : CoreRep 84 D) (j k : Fin 84) (x : D) :
    qgCoord Φ j (qgMom Φ k x) - qgMom Φ k (qgCoord Φ j x)
      = (if j = k then Complex.I else 0) • x := by
  have hc (p : MvPolynomial (Fin 84) ℂ) :
      mulOp (X j) (momOp k p) - momOp k (mulOp (X j) p) =
        (if j = k then Complex.I else 0) • p := by
    classical
    unfold momOp derOp BookProof.YangMillsHermite.mulOp
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe, Derivation.leibniz,
      MvPolynomial.pderiv_X, smul_eq_C_mul, smul_eq_mul]
    split_ifs with h
    · subst k
      simp
      ring
    · have hk : k ≠ j := Ne.symm h
      simp [hk]
      ring
  obtain ⟨p, rfl⟩ := Φ.equiv.surjective x
  simp only [qgCoord, qgMom, CoreRep.op, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply]
  rw [← map_sub, hc, map_smul]

#print axioms solution
