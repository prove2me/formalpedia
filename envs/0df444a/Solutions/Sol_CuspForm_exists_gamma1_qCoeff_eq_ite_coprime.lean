-- Prove2me | solution 1 for CuspForm.exists_gamma1_qCoeff_eq_ite_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3d7e9ad7-bdd0-5d94-b7cc-5ce16d875269

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime

set_option autoImplicit false

noncomputable section

namespace CuspFormDepletionSol

p2m_open "CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function OnePoint Complex Function.Complex Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup"

p2m_open "UpperHalfPlane~I"
open scoped Real

local notation "𝕢" => Function.Periodic.qParam

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

abbrev transGL (t : ℝ) : GL (Fin 2) ℝ := upperRightHom t

lemma val_transGL (t : ℝ) :
    ((transGL t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, t; 0, 1] := by
  simp [transGL]

lemma intCast_zmod_eq_one_of_dvd {N : ℕ} {x : ℤ} (h : (N : ℤ) ∣ x - 1) :
    ((x : ℤ) : ZMod N) = 1 :=
  (intCast_zmod_eq_one_iff_dvd x N).mpr h

lemma exists_cocycle_trans {N ℓ : ℕ} (hℓ : ℓ ≠ 0) (j : ℤ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 (N * ℓ ^ 2)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma1 N ∧
      transGL ((j : ℝ) / ℓ) * mapGL ℝ γ = mapGL ℝ δ * transGL ((j : ℝ) / ℓ) := by
  rw [Gamma1_mem] at hγ
  obtain ⟨ha, hd, hc⟩ := hγ
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this

  have hNl_c : ((N * ℓ ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have hNl_a : ((N * ℓ ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ha, sub_self]
  have hNl_d : ((N * ℓ ^ 2 : ℕ) : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hd, sub_self]
  have hN_Nl : (N : ℤ) ∣ ((N * ℓ ^ 2 : ℕ) : ℤ) := ⟨ℓ ^ 2, by push_cast; ring⟩
  have hl_Nl : (ℓ : ℤ) ∣ ((N * ℓ ^ 2 : ℕ) : ℤ) := ⟨N * ℓ, by push_cast; ring⟩
  have hl2_Nl : ((ℓ : ℤ) ^ 2) ∣ ((N * ℓ ^ 2 : ℕ) : ℤ) := ⟨N, by push_cast; ring⟩
  obtain ⟨c₂, hc₂⟩ : ((ℓ : ℤ) ^ 2) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := hl2_Nl.trans hNl_c
  obtain ⟨e, he⟩ : (ℓ : ℤ) ∣
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    have := dvd_sub (hl_Nl.trans hNl_d) (hl_Nl.trans hNl_a)
    convert this using 1 <;> first | rfl | ring
  have hN_c₂ : (N : ℤ) ∣ c₂ := by
    obtain ⟨q, hq⟩ := hNl_c
    refine ⟨q, ?_⟩
    have hℓ' : ((ℓ : ℤ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hℓ)
    apply mul_left_cancel₀ hℓ'
    rw [← hc₂, hq]; push_cast; ring

  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha'
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb'
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc'
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd'
  have hdetδ : Matrix.det !![a + j * ℓ * c₂, b + j * e - j ^ 2 * c₂; c, d - j * ℓ * c₂] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (j * ℓ * c₂) * he + (j ^ 2 * c₂ - j * e) * hc₂
  refine ⟨⟨_, hdetδ⟩, ?_, ?_⟩
  · rw [Gamma1_mem]
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    have hN_lc₂ : (N : ℤ) ∣ ℓ * c₂ := dvd_mul_of_dvd_right hN_c₂ _
    refine ⟨?_, ?_, ?_⟩
    · apply intCast_zmod_eq_one_of_dvd
      have := dvd_add (hN_Nl.trans hNl_a) (dvd_mul_of_dvd_right hN_lc₂ j)
      convert this using 1 <;> first | rfl | ring
    · apply intCast_zmod_eq_one_of_dvd
      have := dvd_sub (hN_Nl.trans hNl_d) (dvd_mul_of_dvd_right hN_lc₂ j)
      convert this using 1 <;> first | rfl | ring
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hN_Nl.trans hNl_c)
  ·
    have hℓR : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
    have hdR : (d : ℝ) = a + ℓ * e := by
      have : ((d - a : ℤ) : ℝ) = ((ℓ * e : ℤ) : ℝ) := congrArg (Int.cast) he
      push_cast at this; linarith
    have hcR : (c : ℝ) = (ℓ : ℝ) ^ 2 * c₂ := by exact_mod_cast hc₂
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, val_transGL, mapGL_coe_matrix, mapGL_coe_matrix]
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← ha', ← hb', ← hc', ← hd', hcR, hdR] <;>
      field_simp <;> ring

def restrictLevel {A B : ℕ} (h : A ∣ B) {k : ℤ} (f : CuspForm (Gamma1 A) k) :
    CuspForm (Gamma1 B) k where
  toFun := ⇑f
  slash_action_eq' γ hγ := SlashInvariantFormClass.slash_action_eq f γ (GammaOneGL_le_of_dvd h hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps f (hc.mono (GammaOneGL_le_of_dvd h))

@[scoped simp] lemma coe_restrictLevel {A B : ℕ} (h : A ∣ B) {k : ℤ} (f : CuspForm (Gamma1 A) k) :
    ⇑(restrictLevel h f) = ⇑f := rfl

lemma slash_transGL_apply (f : ℍ → ℂ) (k : ℤ) (t : ℝ) (τ : ℍ) :
    (f ∣[k] transGL t) τ = f (t +ᵥ τ) := by
  have hsm : transGL t • τ = t +ᵥ τ := by
    ext
    simp [transGL, σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]
  rw [slash_apply, hsm]
  simp [transGL, σ, denom, GeneralLinearGroup.val_det_apply]

def transGLRat (q : ℚ) : GL (Fin 2) ℚ := upperRightHom q

lemma transGLRat_map (q : ℚ) :
    (transGLRat q).map (Rat.castHom ℝ) = transGL (q : ℝ) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transGLRat, transGL]

lemma isCusp_SL2Z_ratSmul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (gQ : GL (Fin 2) ℚ) :
    IsCusp (gQ.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

def translate {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (j : ℤ) : CuspForm (Gamma1 (N * ℓ ^ 2)) k where
  toFun := ⇑f ∣[k] transGL ((j : ℝ) / ℓ)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨δ, hδ, hcoc⟩ := exists_cocycle_trans (N := N) hℓ j hg
    rw [← SlashAction.slash_mul, hcoc, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq f (mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]
  holo' := (CuspFormClass.holo f).slash k _
  zero_at_cusps' {c} hc := by
    haveI : NeZero (N * ℓ ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hℓ)⟩
    refine IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    have : transGL ((j : ℝ) / ℓ) = (transGLRat ((j : ℚ) / ℓ)).map (Rat.castHom ℝ) := by
      rw [transGLRat_map]; push_cast; rfl
    rw [this]
    exact isCusp_SL2Z_ratSmul hc _

@[scoped simp] lemma translate_apply {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (j : ℤ) (τ : ℍ) :
    translate f hℓ j τ = f ((((j : ℝ) / ℓ : ℝ)) +ᵥ τ) :=
  slash_transGL_apply _ _ _ _

lemma one_mem_strictPeriods_Gamma1 (L : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 L : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

lemma hasSum_qExp {L : ℕ} [NeZero L] {k : ℤ} (F : CuspForm (Gamma1 L) k) (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion 1 ⇑F).coeff n • 𝕢 1 τ ^ n) (F τ) :=
  hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex F (one_mem_strictPeriods_Gamma1 L))
    (CuspFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ

lemma qParam_vadd (t : ℝ) (τ : ℍ) :
    𝕢 1 ((t +ᵥ τ : ℍ) : ℂ) = cexp (2 * π * I * t) * 𝕢 1 τ := by
  simp only [Periodic.qParam, coe_vadd, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma sum_exp_two_pi_mul (ℓ : ℕ) (hℓ : ℓ ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.range ℓ, cexp (2 * π * I * (((j : ℤ) : ℝ) / ℓ : ℝ)) ^ n
      = if ℓ ∣ n then (ℓ : ℂ) else 0 := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  set ζ : ℂ := cexp (2 * π * I * (n / ℓ)) with hζ
  have hterm : ∀ j : ℕ, cexp (2 * π * I * (((j : ℤ) : ℝ) / ℓ : ℝ)) ^ n = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hterm]
  split_ifs with hdvd
  · obtain ⟨m, rfl⟩ := hdvd
    have hζ1 : ζ = 1 := by
      rw [hζ]; push_cast
      rw [show 2 * (π : ℂ) * I * ((ℓ : ℂ) * m / ℓ) = m * (2 * π * I) by field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I m
    simp [hζ1]
  · have hζne : ζ ≠ 1 := by
      intro h
      rw [hζ, Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hnm : (n : ℂ) = m * ℓ := by
        have h3 : (2 * π * I : ℂ) * (n / ℓ) = (2 * π * I) * m := by rw [hm]; ring
        have h4 := mul_left_cancel₀ h2 h3
        field_simp at h4
        linear_combination h4
      have hnmZ : (n : ℤ) = m * ℓ := by exact_mod_cast hnm
      exact hdvd (Int.natCast_dvd_natCast.mp ⟨m, by rw [hnmZ]; ring⟩)
    have hζℓ : ζ ^ ℓ = 1 := by
      rw [hζ, ← Complex.exp_nat_mul]
      rw [show (ℓ : ℂ) * (2 * π * I * (n / ℓ)) = n * (2 * π * I) by field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I n
    rw [geom_sum_eq hζne, hζℓ, sub_self, zero_div]

lemma coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm Γ k) : ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) :=
  map_sum (FunLike.coeAddMonoidHom (CuspForm Γ k) UpperHalfPlane ℂ) F s

def depleteForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    CuspForm (Gamma1 (N * ℓ ^ 2)) k :=
  restrictLevel (dvd_mul_right N (ℓ ^ 2)) f -
    (ℓ : ℂ)⁻¹ • ∑ j ∈ Finset.range ℓ, translate f hℓ (j : ℤ)

lemma depleteForm_apply {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (τ : ℍ) :
    depleteForm f hℓ τ
      = f τ - (ℓ : ℂ)⁻¹ * ∑ j ∈ Finset.range ℓ, f (((((j : ℤ) : ℝ) / ℓ : ℝ)) +ᵥ τ) := by
  simp only [depleteForm, CuspForm.coe_sub, Pi.sub_apply, CuspForm.IsGLPos.coe_smul,
    Pi.smul_apply, coe_finset_sum, Finset.sum_apply, coe_restrictLevel, translate_apply,
    smul_eq_mul]

lemma hasSum_depleteForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (τ : ℍ) :
    HasSum (fun n : ℕ => (if ℓ ∣ n then 0 else (qExpansion 1 ⇑f).coeff n) • 𝕢 1 τ ^ n)
      (depleteForm f hℓ τ) := by
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  set a : ℕ → ℂ := fun n => (qExpansion 1 ⇑f).coeff n with ha
  set e : ℕ → ℂ := fun j => cexp (2 * π * I * (((j : ℤ) : ℝ) / ℓ : ℝ)) with he

  have htr : ∀ j ∈ Finset.range ℓ,
      HasSum (fun n : ℕ => (a n * e j ^ n) • 𝕢 1 τ ^ n) (f (((((j : ℤ) : ℝ) / ℓ : ℝ)) +ᵥ τ)) := by
    intro j _
    have h := hasSum_qExp f (((((j : ℤ) : ℝ) / ℓ : ℝ)) +ᵥ τ)
    rw [qParam_vadd] at h
    convert h using 2 with n <;> try rfl
    simp only [ha, he, smul_eq_mul, mul_pow]; ring
  have hsum := (hasSum_qExp f τ).sub ((hasSum_sum htr).mul_left ((ℓ : ℂ)⁻¹))
  rw [← depleteForm_apply f hℓ τ] at hsum
  convert hsum using 2 with n <;> try rfl

  have hS := sum_exp_two_pi_mul ℓ hℓ n
  simp only [smul_eq_mul]
  rw [show ∑ j ∈ Finset.range ℓ, a n * e j ^ n * 𝕢 1 ↑τ ^ n
      = a n * 𝕢 1 ↑τ ^ n * ∑ j ∈ Finset.range ℓ, e j ^ n by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring]
  simp only [he] at hS ⊢
  rw [hS]
  split_ifs with hdvd
  · field_simp; ring
  · ring

lemma qCoeff_depleteForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (depleteForm f hℓ) n
      = if ℓ ∣ n then 0 else ModularFormClass.qCoeff f n := by
  haveI : NeZero (N * ℓ ^ 2) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hℓ)⟩
  have := ModularFormClass.qExpansion_coeff_unique one_pos
    (one_mem_strictPeriods_Gamma1 (N * ℓ ^ 2)) (f := depleteForm f hℓ)
    (hasSum_depleteForm f hℓ) n
  exact this.symm

lemma exists_deplete_finset {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1 N) k)
    (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ ≠ 0) :
    ∃ (L : ℕ) (_ : NeZero L) (g : CuspForm (Gamma1 L) k),
      L ∣ N * ∏ ℓ ∈ P, ℓ ^ 2 ∧
      ∀ n, ModularFormClass.qCoeff g n
        = if (∀ ℓ ∈ P, ¬ ℓ ∣ n) then ModularFormClass.qCoeff f n else 0 := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    refine ⟨N, inferInstance, f, by simp, fun n => by simp⟩
  | insert ℓ P hℓP ih =>
    obtain ⟨L, hL, g, hLdvd, hg⟩ := ih (fun ℓ' hℓ' => hP ℓ' (Finset.mem_insert_of_mem hℓ'))
    have hℓ : ℓ ≠ 0 := hP ℓ (Finset.mem_insert_self ℓ P)
    haveI : NeZero (L * ℓ ^ 2) := ⟨mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 hℓ)⟩
    refine ⟨L * ℓ ^ 2, inferInstance, depleteForm g hℓ, ?_, fun n => ?_⟩
    · refine (mul_dvd_mul_right hLdvd (ℓ ^ 2)).trans (dvd_of_eq ?_)
      rw [Finset.prod_insert hℓP]; ring
    · rw [qCoeff_depleteForm, hg n]
      by_cases h1 : ℓ ∣ n
      · have h2 : ¬ (∀ ℓ' ∈ insert ℓ P, ¬ ℓ' ∣ n) :=
          fun h => h ℓ (Finset.mem_insert_self _ _) h1
        rw [if_pos h1, if_neg h2]
      · rw [if_neg h1]
        have h2 : (∀ ℓ' ∈ P, ¬ ℓ' ∣ n) ↔ (∀ ℓ' ∈ insert ℓ P, ¬ ℓ' ∣ n) := by
          rw [Finset.forall_mem_insert]; exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
        exact if_congr h2 rfl rfl

lemma coprime_iff_forall_primeFactors {Q : ℕ} (hQ : Q ≠ 0) (n : ℕ) :
    n.Coprime Q ↔ ∀ ℓ ∈ Q.primeFactors, ¬ ℓ ∣ n := by
  constructor
  · intro h ℓ hℓ hℓn
    rw [Nat.mem_primeFactors] at hℓ
    have := Nat.dvd_gcd hℓn hℓ.2.1
    rw [h.gcd_eq_one, Nat.dvd_one] at this
    exact hℓ.1.one_lt.ne' this
  · intro h
    refine (Nat.coprime_of_dvd fun p hp hpQ hpn => ?_).symm
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpQ, hQ⟩) hpn

theorem main (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0)
    (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 := by
  obtain ⟨L, hL, g, hLdvd, hg⟩ := exists_deplete_finset f Q.primeFactors
    (fun ℓ hℓ => (Nat.prime_of_mem_primeFactors hℓ).ne_zero)
  have hprod : ∏ ℓ ∈ Q.primeFactors, ℓ ^ 2 ∣ Q ^ 2 := by
    rw [Finset.prod_pow]; exact pow_dvd_pow_of_dvd (Nat.prod_primeFactors_dvd Q) 2
  have hLM : L ∣ M := hLdvd.trans ((mul_dvd_mul_left N hprod).trans hM)
  refine ⟨restrictLevel hLM g, fun n => ?_⟩
  rw [show ModularFormClass.qCoeff (restrictLevel hLM g) n = ModularFormClass.qCoeff g n from rfl,
    hg n]
  exact if_congr (coprime_iff_forall_primeFactors hQ n).symm rfl rfl

end CuspFormDepletionSol
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.CuspFormDepletionSol"

end
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime.CuspFormDepletionSol"

open CongruenceSubgroup in
theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (Gamma1 N) k) (Q : ℕ) (hQ : Q ≠ 0) (M : ℕ) (hM : N * Q ^ 2 ∣ M) :
    ∃ g : CuspForm (Gamma1 M) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime Q then ModularFormClass.qCoeff f n else 0 :=
  CuspFormDepletionSol.main N k f Q hQ M hM

end S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime
end P2MW
export P2MW.S_CuspForm_exists_gamma1_qCoeff_eq_ite_coprime (solution)
