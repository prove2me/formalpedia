-- Prove2me | solution 1 for CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/dc78b651-7057-5b84-aaa3-8e0e4bca17c9

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
import Theorems.Thm_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
import Theorems.Thm_CuspForm_exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm
import Theorems.Thm_CuspForm_isPrimitiveForm_inv_of_qCoeff_eq_conj
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_heckeU_of_dvd
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass UpperHalfPlane ModularForm
open scoped MatrixGroups ComplexConjugate ModularForm

noncomputable section

namespace OldFormCosetSum

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Function.Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, CuspForm.IsGLPos.coe_smul, qExpansion_smul (analytic f), map_smul,
    smul_eq_mul]

end QCoeff

def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem val_frickeGL (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  linarith

theorem coe_frickeGL_smul (M : ℕ) [NeZero M] (τ : ℍ) :
    (↑(frickeGL M • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]

theorem frickeGL_smul_mul (M : ℕ) [NeZero M] (τ : ℍ) :
    ((frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

variable {M : ℕ} [NeZero M] {k : ℤ}

omit [NeZero M] in
theorem ne_zero_of_isPrimitiveForm {ε : DirichletCharacter ℂ M} {g : CuspForm (Γ₁ℝ M) k}
    (hg : CuspForm.IsPrimitiveForm ε g) : g ≠ 0 := by
  intro h0
  have h1 := hg.isEigenformWith.qCoeff_one
  rw [h0, CuspForm.coe_zero, qCoeff_zero_fun] at h1
  exact zero_ne_one h1

theorem qCoeff_sub (f g : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    qCoeff (⇑(f - g)) n = qCoeff (⇑f) n - qCoeff (⇑g) n := by
  rw [qCoeff, qCoeff, qCoeff, CuspForm.coe_sub, qExpansion_sub (analytic f) (analytic g), map_sub]

theorem heckeDiagMatrix_smul_heckeMatrix_smul {q : ℕ} (hq : q ≠ 0) (τ : ℍ) :
    heckeDiagMatrix q • (heckeMatrix q 0 • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeDiagMatrix_smul hq, coe_heckeMatrix_smul hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast; field_simp; ring

theorem heckeMatrix_smul_heckeDiagMatrix_smul {q : ℕ} (hq : q ≠ 0) (τ : ℍ) :
    heckeMatrix q 0 • (heckeDiagMatrix q • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hq, coe_heckeDiagMatrix_smul hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast; field_simp; ring

theorem heckeDiagMatrix_one_smul (τ : ℍ) : heckeDiagMatrix 1 • τ = τ := by
  apply UpperHalfPlane.ext
  rw [coe_heckeDiagMatrix_smul one_ne_zero]
  push_cast; ring

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (τ : ℍ) :
    ∑ j ∈ Finset.range q,
        ((fun σ : ℍ => g (heckeDiagMatrix q • σ)) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * M) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * conj (qCoeff g q) * g τ
          - conj (ε (q : ZMod M)) * (q : ℂ) ^ (-k) * g (heckeMatrix q 0 • τ) := by
  have hg0 : g ≠ 0 := ne_zero_of_isPrimitiveForm hg
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hq0 : q ≠ 0 := hq.ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  haveI : NeZero (q * M) := ⟨mul_ne_zero hq0 (NeZero.ne M)⟩

  obtain ⟨g', -, hg'⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj M k g
  obtain ⟨c, hc0, hc⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε g hg g' hg'
  have hg'prim : CuspForm.IsPrimitiveForm ε⁻¹ g' :=
    CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj M k ε g hg g' hg'
  have hgg' : ∀ n : ℕ, qCoeff g n = conj (qCoeff g' n) := fun n => by
    rw [hg' n, Complex.conj_conj]
  obtain ⟨c', -, hc'⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm M k ε⁻¹ g' hg'prim g hgg'

  have hcc' : c * c' = (-(M : ℂ)) ^ k := by
    obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ℍ, g τ₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hg0 (DFunLike.ext g 0 fun τ => by rw [h τ, CuspForm.zero_apply])
    set W : ℍ := frickeGL M • τ₀ with hW
    have hrelW : (W : ℂ) * ((M : ℂ) * (τ₀ : ℂ)) = -1 := frickeGL_smul_mul M τ₀
    have hrel0 : (τ₀ : ℂ) * ((M : ℂ) * (W : ℂ)) = -1 := by linear_combination hrelW
    have h1 : g τ₀ = c * (W : ℂ) ^ k * g' W := hc W τ₀ hrel0
    have h2 : g' W = c' * (τ₀ : ℂ) ^ k * g τ₀ := hc' τ₀ W hrelW
    have hWτ : (W : ℂ) * (τ₀ : ℂ) = -1 / (M : ℂ) := by
      have hτ₀ne : (τ₀ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ₀
      field_simp
      linear_combination hrelW
    have h3 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k * g τ₀ = g τ₀ := by
      rw [mul_zpow]
      calc c * c' * ((W : ℂ) ^ k * (τ₀ : ℂ) ^ k) * g τ₀
          = c * (W : ℂ) ^ k * (c' * (τ₀ : ℂ) ^ k * g τ₀) := by ring
        _ = g τ₀ := by rw [← h2, ← h1]
    have h4 : c * c' * ((W : ℂ) * (τ₀ : ℂ)) ^ k = 1 := by
      have := mul_right_cancel₀ hτ₀ (h3.trans (one_mul (g τ₀)).symm)
      exact this
    rw [hWτ] at h4
    have h5 : (-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k = 1 := by
      rw [← mul_zpow, show (-1 / (M : ℂ)) * (-(M : ℂ)) = 1 by field_simp, one_zpow]
    calc c * c' = c * c' * ((-1 / (M : ℂ)) ^ k * (-(M : ℂ)) ^ k) := by rw [h5, mul_one]
      _ = (c * c' * (-1 / (M : ℂ)) ^ k) * (-(M : ℂ)) ^ k := by ring
      _ = (-(M : ℂ)) ^ k := by rw [h4, one_mul]

  obtain ⟨G', hG'fun, hG'coef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (M := M) (N := q * M) (d := 1) ⟨q, by ring⟩ g'
  obtain ⟨Gq', hGq'fun, hGq'coef, -⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus
    (k := k) (M := M) (N := q * M) (d := q) ⟨1, by ring⟩ g'
  have hG'val : ∀ σ : ℍ, G' σ = g' σ := fun σ => by rw [hG'fun σ, heckeDiagMatrix_one_smul]
  have hG'c : ∀ n : ℕ, qCoeff G' n = conj (qCoeff g n) := fun n => by
    rw [hG'coef n, if_pos (one_dvd n), Nat.div_one, hg']
  have hGq'c : ∀ n : ℕ, qCoeff Gq' n = if q ∣ n then conj (qCoeff g (n / q)) else 0 := fun n => by
    rw [hGq'coef n]
    split_ifs <;> simp [hg']

  obtain ⟨U, hUcoe, hUcoef, -⟩ :=
    CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k (dvd_mul_right q M) (c • G')
  have heig := hg.isEigenformWith
  have hqk : conj ((q : ℂ) ^ (k - 1)) = (q : ℂ) ^ (k - 1) := by
    rw [map_zpow₀, Complex.conj_natCast]
  have hUeq : U = (c * conj (qCoeff g q)) • G' - (c * conj (ε (q : ZMod M)) * (q : ℂ) ^ (k - 1)) • Gq' := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods (q * M)) fun n => ?_
    rw [hUcoef n, qCoeff_smul, qCoeff_sub, qCoeff_smul, qCoeff_smul, hG'c, hG'c, hGq'c]
    have hrel := heig.hecke_of_not_dvd hq hqM n
    have hrel' : qCoeff g (q * n) = qCoeff g q * qCoeff g n
        - ε (q : ZMod M) * (q : ℂ) ^ (k - 1) * (if q ∣ n then qCoeff g (n / q) else 0) := by
      linear_combination hrel
    rw [hrel', map_sub, map_mul, map_mul, map_mul, hqk]
    split_ifs with hqn
    · ring
    · simp only [map_zero, mul_zero]; ring
  have hUval : ∀ σ : ℍ, heckeU k q (fun σ => c * g' σ) σ
      = c * conj (qCoeff g q) * g' σ
        - c * conj (ε (q : ZMod M)) * (q : ℂ) ^ (k - 1) * g' (heckeDiagMatrix q • σ) := by
    intro σ
    have hcG' : (fun σ => c * g' σ) = ⇑(c • G') := by
      funext σ; rw [CuspForm.IsGLPos.smul_apply, smul_eq_mul, hG'val]
    rw [hcG', ← hUcoe, hUeq, CuspForm.sub_apply, CuspForm.IsGLPos.smul_apply,
      CuspForm.IsGLPos.smul_apply, smul_eq_mul, smul_eq_mul, hG'val, hGq'fun]

  have hcast : ((q * M : ℕ) : ℂ) = (q : ℂ) * (M : ℂ) := by push_cast; ring
  have key := UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU (q * M) k
    hq0 (dvd_mul_right q M) (fun σ : ℍ => g (heckeDiagMatrix q • σ)) (fun σ => c * g' σ)
    (fun σ => c * c' * (conj (qCoeff g q) * (q : ℂ) ^ k * g (heckeDiagMatrix q • σ)
        - conj (ε (q : ZMod M)) * (q : ℂ) ^ (k - 1) * g σ))
    (fun σ τ' hστ' => by

      have hrel : ((heckeDiagMatrix q • τ' : ℍ) : ℂ) * ((M : ℂ) * (σ : ℂ)) = -1 := by
        rw [coe_heckeDiagMatrix_smul hq0]; rw [hcast] at hστ'; linear_combination hστ'
      rw [hc σ _ hrel]; ring)
    (fun σ τ' hστ' => by
      rw [hUval]

      have hrela : (τ' : ℂ) * ((M : ℂ) * ((heckeDiagMatrix q • σ : ℍ) : ℂ)) = -1 := by
        rw [coe_heckeDiagMatrix_smul hq0]; rw [hcast] at hστ'; linear_combination hστ'
      have hrelb : ((heckeDiagMatrix q • τ' : ℍ) : ℂ) * ((M : ℂ) * (σ : ℂ)) = -1 := by
        rw [coe_heckeDiagMatrix_smul hq0]; rw [hcast] at hστ'; linear_combination hστ'
      rw [hc' _ τ' hrela, hc' σ _ hrelb, coe_heckeDiagMatrix_smul hq0, mul_zpow]
      ring)
    τ
  rw [Nat.mul_div_cancel_left M hq.pos] at key
  rw [key, heckeDiagMatrix_smul_heckeMatrix_smul hq0, hcc', hcast]
  have hMk : (-(M : ℂ)) ^ k ≠ 0 := zpow_ne_zero k (neg_ne_zero.mpr hMC)
  have hqk' : (q : ℂ) ^ k ≠ 0 := zpow_ne_zero k hqC
  rw [show -((q : ℂ) * (M : ℂ)) = (q : ℂ) * (-(M : ℂ)) by ring, mul_zpow, zpow_neg, zpow_neg,
    zpow_sub₀ hqC, zpow_sub₀ hqC, zpow_one]
  field_simp

end OldFormCosetSum
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.OldFormCosetSum"

end
p2m_reactivate "P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd.OldFormCosetSum"

open scoped MatrixGroups ModularForm in
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hg : CuspForm.IsPrimitiveForm ε g)
    {q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        ((fun σ : UpperHalfPlane => g (ModularForm.heckeDiagMatrix q • σ)) ∣[k]
          (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * M) * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g q) * g τ
          - starRingEnd ℂ (ε (q : ZMod M)) * (q : ℂ) ^ (-k) *
              g (ModularForm.heckeMatrix q 0 • τ) :=
  OldFormCosetSum.main ε g hg hq hqM τ

end S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
end P2MW
export P2MW.S_CuspForm_IsPrimitiveForm_sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd (solution)
