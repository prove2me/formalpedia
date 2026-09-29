-- Prove2me | solution 1 for CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fa1fe949-93be-5d87-9f23-e9b9508b681a

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one
import Theorems.Thm_CuspForm_hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke
import Theorems.Thm_CuspForm_conj_heckeEigenvalue_eq_of_hasNebentypus
import Theorems.Thm_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj
import Theorems.Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

noncomputable section

namespace FrickePseudoEigenvalue

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, qCoeff g' n = conj (qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : ℍ, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 → g τ' = c * (τ : ℂ) ^ k * g' τ := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have heig := hg.isEigenformWith

  obtain ⟨h, hh⟩ := CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one M k g

  obtain ⟨hneb, hhecke⟩ :=
    CuspForm.hasNebentypus_inv_and_qCoeff_hecke_eigen_of_fricke M k ε g h heig.hasNebentypus hh

  have hadj : ∀ p : ℕ, p.Prime → ¬ p ∣ M →
      conj (qCoeff g p) = ε⁻¹ (p : ZMod M) * qCoeff g p := fun p hp hpM =>
    CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M k ε g hg0 heig.hasNebentypus p hp hpM
      (qCoeff g p) (heig.hecke_of_not_dvd hp hpM)

  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'

  have hmult : h = qCoeff h 1 • g' := by
    refine CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen M k ε⁻¹ g' hg'prim h hneb ∅
      (fun p hp _ hpM n => ?_)
    rw [hg' p, hadj p hp hpM]
    exact hhecke p hp hpM (qCoeff g p) (heig.hecke_of_not_dvd hp hpM) n

  refine ⟨qCoeff h 1, fun hc => hg0 ?_, fun τ τ' hτ => ?_⟩
  ·
    rw [hc, zero_smul] at hmult
    apply DFunLike.ext
    intro τ'
    have key := hh (frickeGL M • τ') τ' (by
      have := frickeGL_smul_mul M τ'
      linear_combination this)
    rw [key, hmult, CuspForm.zero_apply, mul_zero, CuspForm.zero_apply]
  · have hpt : h τ = qCoeff h 1 * g' τ := by
      have := congrArg (fun F : CuspForm (Gamma1 M) k => F τ) hmult
      simpa only [CuspForm.IsGLPos.smul_apply, smul_eq_mul] using this
    rw [hh τ τ' hτ, hpt]
    ring

end FrickePseudoEigenvalue
p2m_reactivate "P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.FrickePseudoEigenvalue"

end
p2m_reactivate "P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm.FrickePseudoEigenvalue"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (g' : CuspForm (Gamma1 M) k)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 →
        g τ' = c * (τ : ℂ) ^ k * g' τ :=
  FrickePseudoEigenvalue.main ε g hg g' hg'

end S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
end P2MW
export P2MW.S_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm (solution)
