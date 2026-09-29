-- Prove2me | solution 1 for CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/300b13d7-9473-5e8e-8079-183d1f5829d0

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo
import Theorems.Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke
import Theorems.Thm_ModularForm_levelOne_weight_four_qCoeff_one
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo
set_option autoImplicit false
set_option Elab.async false
open scoped ModularForm MatrixGroups

namespace S09WFP1

private lemma hp0 {p : ℕ} [Fact p.Prime] : p ≠ 0 := (Fact.out : p.Prime).ne_zero

private scoped instance instNeZeroOfFactPrime {p : ℕ} [Fact p.Prime] : NeZero p := ⟨hp0⟩

private lemma hΓ0 (p : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 p : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

private lemma qCoeff_coe_mul {p : ℕ} (X Z : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑X * ⇑Z) n
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ModularFormClass.qCoeff ⇑X ij.1 * ModularFormClass.qCoeff ⇑Z ij.2 := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_mul_coe one_pos (hΓ0 p) X Z, PowerSeries.coeff_mul]

private lemma exists_int_coeffs_mul {p : ℕ} (X Z : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (aX aZ : ℕ → ℤ) (haX : ∀ n : ℕ, (aX n : ℂ) = ModularFormClass.qCoeff ⇑X n)
    (haZ : ∀ n : ℕ, (aZ n : ℂ) = ModularFormClass.qCoeff ⇑Z n) (M : ℤ)
    (hX : ∀ n : ℕ, n ≠ 0 → M ∣ aX n) (hZ : ∀ n : ℕ, n ≠ 0 → M ∣ aZ n) :
    ∃ aH : ℕ → ℤ, (∀ n : ℕ, (aH n : ℂ) = ModularFormClass.qCoeff (⇑X * ⇑Z) n) ∧
      aH 0 = aX 0 * aZ 0 ∧ ∀ n : ℕ, n ≠ 0 → M ∣ aH n := by
  refine ⟨fun n => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, aX ij.1 * aZ ij.2, fun n => ?_, ?_, fun n hn => ?_⟩
  · rw [qCoeff_coe_mul]
    simp only [Int.cast_sum, Int.cast_mul, haX, haZ]
  · simp
  · refine Finset.dvd_sum fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases h1 : ij.1 = 0
    · have h2 : ij.2 ≠ 0 := by
        intro h2
        exact hn (by rw [← hij, h1, h2])
      exact dvd_mul_of_dvd_right (hZ _ h2) _
    · exact dvd_mul_of_dvd_left (hX _ h1) _

private noncomputable def WF (p : ℕ) [Fact p.Prime] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (p : ℝ), 0] (by
    rw [Matrix.det_fin_two_of]
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hp0 (p := p))
    simpa using this)

private lemma WF_coe (p : ℕ) [Fact p.Prime] :
    ((WF p : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0] :=
  rfl

private lemma det_WF (p : ℕ) [Fact p.Prime] : ((WF p).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, WF_coe, Matrix.det_fin_two_of]
  ring

private lemma negp_ne (p : ℕ) [Fact p.Prime] : -(p : ℝ) ≠ 0 :=
  neg_ne_zero.mpr (by exact_mod_cast (hp0 (p := p)))

private lemma WF_mul_WF (p : ℕ) [Fact p.Prime] :
    WF p * WF p = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(p : ℝ)) (negp_ne p)) := by
  apply Units.ext
  rw [Units.val_mul, WF_coe,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(p : ℝ)) (negp_ne p)) :
        Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.scalar (Fin 2) (-(p : ℝ)) from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]

private lemma slash_scalar_two (c : ℝˣ) (g : UpperHalfPlane → ℂ) :
    g ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = g := by
  ext τ
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c).det.val : ℝ) = (c : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp [Fintype.card_fin]
  have hpos : 0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) c).det.val : ℝ) := by
    rw [hdet]
    exact pow_two_pos_of_ne_zero c.ne_zero
  have hc : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr c.ne_zero
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hpos, hdet,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar,
    abs_of_nonneg (sq_nonneg (c : ℝ))]
  simp only [ContinuousAlgEquiv.refl_apply]
  have : (((c : ℝ) ^ 2 : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(2 : ℤ)) = 1 := by
    push_cast
    rw [← zpow_natCast (((c : ℝ) : ℂ)) 2, ← zpow_add₀ hc]
    norm_num
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, mul_assoc, this, mul_one]

private def alp (p : ℕ) : ModularForm.AtkinLehnerDatum p p :=
  ⟨1, (mul_one p).symm, 0, -1, by simp⟩

private lemma alp_alGL_coe (p : ℕ) [Fact p.Prime] :
    (((alp p).alGL : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![0, -1; (p : ℝ), (p : ℝ)] := by
  rw [ModularForm.AtkinLehnerDatum.alGL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alp, ModularForm.AtkinLehnerDatum.mat, Matrix.map_apply]

private def Tinv : SL(2, ℤ) := ⟨!![1, -1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] private lemma Tinv_coe : ((Tinv : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 0, 1] := rfl

private lemma Tinv_mem (p : ℕ) : Tinv ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp

private lemma Tinv_mapGL_coe :
    ((Matrix.SpecialLinearGroup.mapGL ℝ Tinv : Matrix.GeneralLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![1, -1; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Tinv_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma alGL_mul_Tinv (p : ℕ) [Fact p.Prime] :
    (alp p).alGL * Matrix.SpecialLinearGroup.mapGL ℝ Tinv = WF p := by
  apply Units.ext
  rw [Units.val_mul, alp_alGL_coe, Tinv_mapGL_coe, WF_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {p : ℕ} [Fact p.Prime]

private noncomputable def fricke (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ModularForm (CongruenceSubgroup.Gamma0 p) 2 :=
  ModularForm.atkinLehnerLin (alp p) 2 X

private lemma coe_fricke (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ⇑(fricke X) = ⇑X ∣[(2 : ℤ)] WF p := by
  have h1 : ⇑(fricke X) = ⇑X ∣[(2 : ℤ)] (alp p).alGL := by
    show ⇑(ModularForm.atkinLehnerLin (alp p) 2 X) = _
    rw [ModularForm.coe_atkinLehnerLin_apply, ModularForm.alSlash_def]
  have h2 : ⇑(fricke X) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ Tinv) = ⇑(fricke X) :=
    SlashInvariantFormClass.slash_action_eq (F := ModularForm (CongruenceSubgroup.Gamma0 p) 2)
      (fricke X) _ (Subgroup.mem_map_of_mem _ (Tinv_mem p))
  rw [← alGL_mul_Tinv p, SlashAction.slash_mul, ← h1, h2]

private lemma fricke_slash (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ⇑(fricke X) ∣[(2 : ℤ)] WF p = ⇑X := by
  rw [coe_fricke, ← SlashAction.slash_mul, WF_mul_WF, slash_scalar_two]

private lemma coe_fricke_eq_neg_heckeU (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ⇑(fricke X) = -ModularForm.heckeU 2 p ⇑X := by
  obtain ⟨Y, hY⟩ := ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p 2
    (fricke X) (WF p) (WF_coe p)
  have hY0 : Y = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero Y
  rw [hY0, ModularForm.coe_zero, fricke_slash, sub_self, zpow_zero, one_smul] at hY
  exact eq_neg_of_add_eq_zero_left hY.symm

private lemma qCoeff_fricke (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (n : ℕ) :
    ModularFormClass.qCoeff ⇑(fricke X) n = -ModularFormClass.qCoeff ⇑X (n * p) := by
  have h1 := ModularFormClass.qCoeff_heckeU X (hΓ0 p) (hp0 (p := p)) n
  rw [ModularForm.coeffHeckeU_apply] at h1
  have h2 : ModularForm.heckeU 2 p ⇑X = -⇑(fricke X) := by
    rw [coe_fricke_eq_neg_heckeU, neg_neg]
  rw [h2] at h1
  unfold ModularFormClass.qCoeff at h1 ⊢
  rw [ModularForm.qExpansion_neg one_pos (hΓ0 p) (fricke X), map_neg] at h1
  exact neg_eq_iff_eq_neg.mp h1

private lemma exists_int_coeffs_fricke (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (aX : ℕ → ℤ) (haX : ∀ n : ℕ, (aX n : ℂ) = ModularFormClass.qCoeff ⇑X n) (M : ℤ)
    (hdvd : ∀ n : ℕ, n ≠ 0 → M ∣ aX n) :
    ∃ aG : ℕ → ℤ, (∀ n : ℕ, (aG n : ℂ) = ModularFormClass.qCoeff ⇑(fricke X) n) ∧
      aG 0 = -aX 0 ∧ ∀ n : ℕ, n ≠ 0 → M ∣ aG n := by
  refine ⟨fun n => -aX (n * p), fun n => ?_, ?_, fun n hn => ?_⟩
  · simp only [Int.cast_neg, haX, qCoeff_fricke]
  · show -aX (0 * p) = -aX 0
    rw [zero_mul]
  · show M ∣ -aX (n * p)
    exact dvd_neg.mpr (hdvd _ (mul_ne_zero hn (hp0 (p := p))))

private lemma exists_weight_four (X Z : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ∃ H : ModularForm (CongruenceSubgroup.Gamma0 p) 4, ⇑H = ⇑X * ⇑Z :=
  ⟨X.mul Z, ModularForm.coe_mul X Z⟩

private lemma coe_mul_fricke_slash (X : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    (⇑X * ⇑(fricke X)) ∣[(4 : ℤ)] WF p = (p : ℂ) • (⇑X * ⇑(fricke X)) := by
  refine (ModularForm.mul_slash 2 2 (WF p) ⇑X ⇑(fricke X)).trans ?_
  rw [← coe_fricke X, fricke_slash X, det_WF, Nat.abs_cast]
  funext τ
  simp only [Pi.smul_apply, Pi.mul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_natCast]
  ring

private lemma trace4_coeff (H : ModularForm (CongruenceSubgroup.Gamma0 p) 4)
    (hHW : ⇑H ∣[(4 : ℤ)] WF p = (p : ℂ) • ⇑H) :
    ∃ Y : ModularForm 𝒮ℒ 4, ∀ n : ℕ, ModularFormClass.qCoeff ⇑Y n
      = (p : ℂ) ^ 2 * ModularFormClass.qCoeff ⇑H n + (p : ℂ) * ModularFormClass.qCoeff ⇑H (n * p) := by
  obtain ⟨Y, hY⟩ := ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p 4 H
    (WF p) (WF_coe p)
  rw [hHW] at hY
  have hs : (p : ℂ) ^ ((4 : ℤ) - 2) = (p : ℂ) ^ 2 := by
    rw [show (4 : ℤ) - 2 = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  rw [hs] at hY
  refine ⟨Y, fun n => ?_⟩
  have hlaw := ModularFormClass.qCoeff_heckeU ((p : ℂ) • H) (hΓ0 p) (hp0 (p := p)) n
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.coeffHeckeU_apply] at hlaw
  have hU : ModularForm.heckeU 4 p ((p : ℂ) • ⇑H) = ⇑Y - (p : ℂ) ^ 2 • ⇑H := by
    rw [hY, add_sub_cancel_left]
  rw [hU] at hlaw
  have hYa := ModularFormClass.analyticAt_cuspFunction_zero Y one_pos one_mem_strictPeriods_SL
  have hHa := ModularFormClass.analyticAt_cuspFunction_zero H one_pos (hΓ0 p)
  have hsHa : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ((p : ℂ) ^ 2 • ⇑H)) 0 := by
    have h := ModularFormClass.analyticAt_cuspFunction_zero ((p : ℂ) ^ 2 • H) one_pos (hΓ0 p)
    rwa [ModularForm.IsGLPos.coe_smul] at h
  unfold ModularFormClass.qCoeff at hlaw ⊢
  rw [UpperHalfPlane.qExpansion_sub hYa hsHa, map_sub, UpperHalfPlane.qExpansion_smul hHa, map_smul,
    smul_eq_mul, ModularForm.qExpansion_smul one_pos (hΓ0 p) (p : ℂ) H, map_smul, smul_eq_mul] at hlaw
  linear_combination hlaw

end S09WFP1
p2m_reactivate "P2MW.S_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo.S09WFP1"

open ModularCurve

namespace CuspForm p2m_export "CuspForm" "IsGLPos.coe_smul smul_apply coe_zero ext coe_smul atkinLehnerLin coe_atkinLehnerLin_apply exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo" end CuspForm
p2m_open_scoped "CuspForm" in
open S09WFP1 in
private theorem CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : (24 * m : ℤ) ∣ 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) := by
  have _ := hm
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp0
  obtain ⟨F, aF, haF, haF0, hdvdF⟩ :=
    CuspForm.exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo p m f af haf hcongr
  have hdvdF' : ∀ n : ℕ, n ≠ 0 → (24 * (m : ℤ)) ∣ aF n := fun n hn => by
    have h := hdvdF n hn
    push_cast at h
    exact h
  obtain ⟨aG, haG, haG0, hdvdG⟩ := exists_int_coeffs_fricke F aF haF _ hdvdF'
  obtain ⟨aH, haH, haH0, hdvdH⟩ := exists_int_coeffs_mul F (fricke F) aF aG haF haG _ hdvdF' hdvdG
  obtain ⟨H, hHcoe⟩ := exists_weight_four F (fricke F)
  have hHW : ⇑H ∣[(4 : ℤ)] WF p = (p : ℂ) • ⇑H := by
    rw [hHcoe]
    exact coe_mul_fricke_slash F
  obtain ⟨Y, hY⟩ := trace4_coeff H hHW
  have hWL := ModularForm.levelOne_weight_four_qCoeff_one Y
  rw [hY 1, hY 0, one_mul, zero_mul, hHcoe, ← haH 1, ← haH p, ← haH 0] at hWL
  have hZ : (p : ℤ) ^ 2 * aH 1 + (p : ℤ) * aH p = 240 * ((p : ℤ) ^ 2 * aH 0 + (p : ℤ) * aH 0) := by
    exact_mod_cast hWL
  rw [haH0, haG0, haF0] at hZ
  have hkey : (p : ℤ) * ((p : ℤ) * aH 1 + aH p + 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1)) = 0 := by
    linear_combination hZ
  have hkey' : (p : ℤ) * aH 1 + aH p + 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) = 0 :=
    (mul_eq_zero.mp hkey).resolve_left hpZ
  have hT : 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) = -((p : ℤ) * aH 1 + aH p) := by
    linear_combination hkey'
  rw [hT]
  exact dvd_neg.mpr (dvd_add (dvd_mul_of_dvd_right (hdvdH 1 one_ne_zero) _) (hdvdH p hp0))

theorem solution (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : (24 * m : ℤ) ∣ 240 * (af 1) ^ 2 * ((p : ℤ) - 1) ^ 2 * ((p : ℤ) + 1) :=
  CuspForm.dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr

end S_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo
end P2MW
export P2MW.S_CuspForm_dvd_240_mul_qCoeff_one_sq_of_qCoeff_congr_sigmaPrimeTo (solution)
