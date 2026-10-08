-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qgCCR_tetrad
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:20:44.648078+00:00
-- url     : https://prove2.me/submissions/5710831e-26da-4aae-9c3d-943c44eece06

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.qgCCR_tetrad
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
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

private theorem ccr_local (Φ : CoreRep 84 D) (j k : Fin 84) (x : D) :
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

theorem solution (Φ : CoreRep 84 D) (mu a nu b : Fin 4) (x : D) :
    qgCoord Φ (idxE mu a) (qgMom Φ (idxE nu b) x) - qgMom Φ (idxE nu b) (qgCoord Φ (idxE mu a) x)
      = (if mu = nu ∧ a = b then Complex.I else 0) • x := by
  have hidx : idxE mu a = idxE nu b ↔ mu = nu ∧ a = b := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      simp only [idxE] at hv
      have hm := mu.isLt
      have hn := nu.isLt
      have ha := a.isLt
      have hb := b.isLt
      constructor <;> apply Fin.ext <;> omega
    · rintro ⟨rfl, rfl⟩
      rfl
  simpa only [hidx] using ccr_local Φ (idxE mu a) (idxE nu b) x

#print axioms solution
