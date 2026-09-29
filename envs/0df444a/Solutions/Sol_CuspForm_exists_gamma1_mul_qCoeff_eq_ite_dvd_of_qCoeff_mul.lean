-- Prove2me | solution 1 for CuspForm.exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/cb729cca-9bb4-53c4-8c56-839a3ede1a3b

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul

set_option autoImplicit false

noncomputable section

namespace Gamma1SharpDepletion

p2m_open "CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function OnePoint Complex Function.Complex Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup"

p2m_open "UpperHalfPlane~I"
open scoped Real

lemma intCast_zmod_eq_one_iff_dvd (x : ℤ) (N : ℕ) :
    ((x : ℤ) : ZMod N) = 1 ↔ (N : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma Gamma1_le_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma1 B ≤ Gamma1 A := by
  intro γ hγ
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have hAB : (A : ℤ) ∣ (B : ℤ) := Int.natCast_dvd_natCast.mpr h
  refine ⟨?_, ?_, ?_⟩
  · rw [intCast_zmod_eq_one_iff_dvd] at h1 ⊢; exact hAB.trans h1
  · rw [intCast_zmod_eq_one_iff_dvd] at h2 ⊢; exact hAB.trans h2
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3 ⊢; exact hAB.trans h3

lemma GammaOneGL_le_of_dvd {A B : ℕ} (h : A ∣ B) :
    ((Gamma1 B : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 A : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma1_le_of_dvd h)

def restrictLevel {A B : ℕ} (h : A ∣ B) {k : ℤ} (f : CuspForm (Gamma1 A) k) :
    CuspForm (Gamma1 B) k where
  toFun := ⇑f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (GammaOneGL_le_of_dvd h hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono (GammaOneGL_le_of_dvd h))

@[scoped simp] lemma coe_restrictLevel {A B : ℕ} (h : A ∣ B) {k : ℤ} (f : CuspForm (Gamma1 A) k) :
    ⇑(restrictLevel h f) = ⇑f := rfl

lemma one_mem_strictPeriods_Gamma1 (L : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

def diagMatInt (q : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(q : ℤ), 0; 0, 1]

lemma diagMatInt_map_eq {q : ℕ} (hq : q ≠ 0) :
    (diagMatInt q).map (algebraMap ℤ ℝ)
      = ((heckeDiagMatrix q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hq]; unfold diagMatInt
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma exists_cocycle_diag {N q : ℕ} (hq : q ≠ 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 (N * q)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧
      diagMatInt q * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (δ : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt q := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha'
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb'
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc'
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd'
  have hdet : a * d - b * c = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hNq_c : ((N * q : ℕ) : ℤ) ∣ c := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have hNq_a : ((N * q : ℕ) : ℤ) ∣ a - 1 := (intCast_zmod_eq_one_iff_dvd _ _).mp ha
  have hNq_d : ((N * q : ℕ) : ℤ) ∣ d - 1 := (intCast_zmod_eq_one_iff_dvd _ _).mp hd
  have hN_Nq : (N : ℤ) ∣ ((N * q : ℕ) : ℤ) := ⟨q, by push_cast; ring⟩
  have hq_Nq : (q : ℤ) ∣ ((N * q : ℕ) : ℤ) := ⟨N, by push_cast; ring⟩
  obtain ⟨c', hcc'⟩ : (q : ℤ) ∣ c := hq_Nq.trans hNq_c
  have hN_c' : (N : ℤ) ∣ c' := by
    obtain ⟨t, ht⟩ := hNq_c
    refine ⟨t, ?_⟩
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    apply mul_left_cancel₀ hqZ
    rw [← hcc', ht]; push_cast; ring
  have hdetδ : Matrix.det !![a, q * b; c', d] = 1 := by
    rw [Matrix.det_fin_two_of]
    have : (q : ℤ) * b * c' = b * c := by rw [hcc']; ring
    linear_combination hdet - this
  refine ⟨⟨_, hdetδ⟩, ?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    exact ⟨(intCast_zmod_eq_one_iff_dvd _ _).mpr (hN_Nq.trans hNq_a),
      (intCast_zmod_eq_one_iff_dvd _ _).mpr (hN_Nq.trans hNq_d),
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hN_c'⟩
  · unfold diagMatInt
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha', ← hb', ← hc', ← hd', hcc'] <;> ring

lemma exists_cocycle_diagGL {N q : ℕ} (hq : q ≠ 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 (N * q)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧
      heckeDiagMatrix q * mapGL ℝ γ = mapGL ℝ δ * heckeDiagMatrix q := by
  obtain ⟨δ, hδ, hconj⟩ := exists_cocycle_diag hq hγ
  refine ⟨δ, hδ, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (heckeDiagMatrix q : Matrix (Fin 2) (Fin 2) ℝ) * ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    = ((mapGL ℝ δ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * (heckeDiagMatrix q : Matrix (Fin 2) (Fin 2) ℝ)
  rw [← diagMatInt_map_eq hq, mapGL_coe_matrix, mapGL_coe_matrix]
  have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℤ => A.map (algebraMap ℤ ℝ)) hconj
  simp only [Matrix.map_mul] at h
  convert h using 2 <;> (ext i j; simp)

def heckeDiagMatrixQ {q : ℕ} (hq : q ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hq)

lemma heckeDiagMatrixQ_map {q : ℕ} (hq : q ≠ 0) :
    (heckeDiagMatrixQ hq).map (Rat.castHom ℝ) = heckeDiagMatrix q := by
  apply Units.ext
  rw [val_heckeDiagMatrix hq]
  show (heckeDiagMatrixQ hq : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeDiagMatrixQ
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma isCusp_SL2Z_ratSmul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (gQ : GL (Fin 2) ℚ) :
    IsCusp (gQ.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

def rescale {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {q : ℕ} (hq : q ≠ 0) :
    CuspForm (Gamma1 (N * q)) k where
  toFun := ⇑f ∣[k] heckeDiagMatrix q
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨δ, hδ, hcoc⟩ := exists_cocycle_diagGL (N := N) hq hg
    rw [← SlashAction.slash_mul, hcoc, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]
  holo' := (CuspFormClass.holo f).slash k _
  zero_at_cusps' {c} hc := by
    haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) hq⟩
    refine IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    rw [← heckeDiagMatrixQ_map hq]
    exact isCusp_SL2Z_ratSmul hc _

lemma rescale_apply {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {q : ℕ} (hq : q ≠ 0)
    (τ : ℍ) : rescale f hq τ = (q : ℂ) ^ (k - 1) * f (heckeDiagMatrix q • τ) :=
  slash_heckeDiagMatrix_apply k hq _ τ

def qCoeffLin (L n : ℕ) [NeZero L] (k : ℤ) : CuspForm (Gamma1 L) k →ₗ[ℂ] ℂ where
  toFun G := ModularFormClass.qCoeff G n
  map_add' f g := by
    show ModularFormClass.qCoeff (⇑(f + g)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1 L) f g, map_add]
  map_smul' c f := by
    show ModularFormClass.qCoeff (⇑(c • f)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1 L),
      _root_.map_smul]
    rfl

theorem qCoeff_sub_smul {L : ℕ} [NeZero L] {k : ℤ} (A B : CuspForm (Gamma1 L) k) (c : ℂ)
    (n : ℕ) : ModularFormClass.qCoeff (⇑(A - c • B)) n
      = ModularFormClass.qCoeff (⇑A) n - c * ModularFormClass.qCoeff (⇑B) n := by
  have h1 : ModularFormClass.qCoeff (⇑(A - c • B)) n = qCoeffLin L n k (A - c • B) := rfl
  rw [h1, map_sub, _root_.map_smul]
  rfl

theorem qCoeff_rescale {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {q : ℕ}
    (hq : q ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (rescale f hq) n
      = if q ∣ n then (q : ℂ) ^ (k - 1) * ModularFormClass.qCoeff f (n / q) else 0 := by
  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) hq⟩
  have hqC : (q : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hq)
  have hfun : (fun τ : ℍ => f (heckeDiagMatrix q • τ))
      = ((q : ℂ) ^ (k - 1))⁻¹ • ⇑(rescale f hq) := by
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, rescale_apply, ← mul_assoc, inv_mul_cancel₀ hqC, one_mul]
  have h1 := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f (one_mem_strictPeriods_Gamma1 N) hq n
  rw [hfun] at h1
  have h2 : ModularFormClass.qCoeff (((q : ℂ) ^ (k - 1))⁻¹ • ⇑(rescale f hq)) n
      = ((q : ℂ) ^ (k - 1))⁻¹ * ModularFormClass.qCoeff (rescale f hq) n := by
    unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1 (N * q)), _root_.map_smul,
      smul_eq_mul]
  rw [h2] at h1
  have h3 := congrArg (fun z : ℂ => (q : ℂ) ^ (k - 1) * z) h1
  rw [← mul_assoc, mul_inv_cancel₀ hqC, one_mul] at h3
  rw [h3]
  split_ifs <;> simp

theorem main (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k)
    (q : ℕ) (hq0 : q ≠ 0)
    (hfU : ∀ n : ℕ, ModularFormClass.qCoeff f (q * n) =
      ModularFormClass.qCoeff f q * ModularFormClass.qCoeff f n) :
    ∃ g : CuspForm (Gamma1 (N * q)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n := by
  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) hq0⟩
  have hqC : (q : ℂ) ^ (k - 1) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hq0)
  refine ⟨restrictLevel (dvd_mul_right N q) f
      - (ModularFormClass.qCoeff f q * ((q : ℂ) ^ (k - 1))⁻¹) • rescale f hq0, fun n => ?_⟩
  rw [qCoeff_sub_smul, qCoeff_rescale f hq0 n]
  have hA : ModularFormClass.qCoeff (⇑(restrictLevel (dvd_mul_right N q) f)) n
      = ModularFormClass.qCoeff f n := rfl
  rw [hA]
  split_ifs with hqn
  · obtain ⟨m, rfl⟩ := hqn
    rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hq0), hfU m]
    field_simp
    ring
  · rw [mul_zero, sub_zero]

end Gamma1SharpDepletion
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul.Gamma1SharpDepletion"

end
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul.Gamma1SharpDepletion"

theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (q : ℕ) (hq : q ≠ 0)
    (hfU : ∀ n : ℕ, ModularFormClass.qCoeff f (q * n) =
      ModularFormClass.qCoeff f q * ModularFormClass.qCoeff f n) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma1 (N * q)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n :=
  Gamma1SharpDepletion.main N k f q hq hfU

end S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul
end P2MW
export P2MW.S_CuspForm_exists_gamma1_mul_qCoeff_eq_ite_dvd_of_qCoeff_mul (solution)
