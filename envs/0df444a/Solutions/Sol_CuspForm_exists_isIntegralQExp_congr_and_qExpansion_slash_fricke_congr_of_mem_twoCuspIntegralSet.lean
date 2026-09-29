-- Prove2me | solution 1 for CuspForm.exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/b698efc3-a78a-524b-bdf0-e1df35f00da5

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_ModularForm_exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv
import Theorems.Thm_ModularForm_exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Theorems.Thm_ModularForm_eisenstein_qCoeff_p_integral_dvd
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
import Theorems.Thm_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open CongruenceSubgroup CohCarrier UpperHalfPlane

namespace SerreFrickeCSF

section Arith

variable {p M : ℕ}

theorem M_eq (hpM : p ∣ M) : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm

theorem coprime_p_Q [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : Nat.Coprime p (M / p) := by
  rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
  rintro ⟨c, hc⟩
  exact hpM2 ⟨c, by rw [pow_two, mul_assoc, ← hc]; exact M_eq hpM⟩

theorem not_p_dvd_Q [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p :=
  (Nat.Prime.coprime_iff_not_dvd Fact.out).mp (coprime_p_Q hpM hpM2)

def alDatumP [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ModularForm.AtkinLehnerDatum M p where
  R := M / p
  hM := M_eq hpM
  a := Nat.gcdA p (M / p)
  b := -Nat.gcdB p (M / p)
  bezout := by
    have h := Nat.gcd_eq_gcd_ab p (M / p)
    rw [(coprime_p_Q hpM hpM2).gcd_eq_one, Nat.cast_one] at h
    linear_combination (-1 : ℤ) * h

end Arith

section GLtools

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

variable (q : ℕ) [NeZero q]

def scalarGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
    simpa using mul_ne_zero hq' hq')

@[scoped simp] lemma scalarGL_coe : (scalarGL q : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)] := rfl

lemma scalarGL_mul_comm (y : GL (Fin 2) ℝ) : scalarGL q * y = y * scalarGL q := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scalarGL_coe]
  have : (!![(q : ℝ), 0; 0, (q : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]

lemma val_det_scalarGL : ((Matrix.GeneralLinearGroup.det (scalarGL q) : ℝˣ) : ℝ) = (q : ℝ) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]; ring

lemma det_scalarGL_pos : 0 < ((Matrix.GeneralLinearGroup.det (scalarGL q) : ℝˣ) : ℝ) := by
  rw [val_det_scalarGL]; have : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  positivity

lemma scalarGL_smul (τ : ℍ) : scalarGL q • τ = τ := by
  have hqC : ((q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_scalarGL_pos q)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, scalarGL_coe, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, add_zero,
    zero_add]
  rw [mul_div_cancel_left₀ _ hqC]

lemma slash_scalarGL (k : ℤ) (f : ℍ → ℂ) : f ∣[k] scalarGL q = ((q : ℂ) ^ (k - 2)) • f := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  ext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ (scalarGL q) (f (scalarGL q • τ)) = f (scalarGL q • τ) := by
    rw [UpperHalfPlane.σ, if_pos (det_scalarGL_pos q)]; rfl
  have hden : denom (scalarGL q) τ = (q : ℝ) := by simp [UpperHalfPlane.denom, scalarGL_coe]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  rw [hσ, scalarGL_smul, val_det_scalarGL, hden, abs_of_pos (pow_pos hq0 2)]
  have h1 : (((q : ℝ) ^ 2 : ℝ) : ℂ) = (q : ℂ) ^ (2 : ℤ) := by rw [zpow_two]; push_cast; ring
  have h2 : (((q : ℝ) : ℝ) : ℂ) = (q : ℂ) := by push_cast; ring
  rw [h1, h2, ← zpow_mul, mul_assoc, ← zpow_add₀ hqC, show (2 : ℤ) * (k - 1) + -k = k - 2 by ring]
  ring

variable {q} {M : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)

lemma alGL_mul_alGL : W.alGL * W.alGL = scalarGL q * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL q : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, scalarGL_coe, mapGL_coe_eq,
    ModularForm.AtkinLehnerDatum.sqUnitSL_coe, ← map_int_mul_eq, W.mat_sq]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast, Int.cast_mul, Int.cast_natCast]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

lemma alGL_inv_eq : W.alGL⁻¹ = (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL)⁻¹ * (scalarGL q)⁻¹ * W.alGL := by
  have h : (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) = (scalarGL q)⁻¹ * (W.alGL * W.alGL) := by
    rw [alGL_mul_alGL, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h]; group

lemma smul_slash_alGL (k : ℤ) (c : ℂ) (f : ℍ → ℂ) : (c • f) ∣[k] W.alGL = c • (f ∣[k] W.alGL) := by
  rw [ModularForm.smul_slash, W.σ_alGL_apply]

lemma slash_alGL_inv (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] W.alGL⁻¹ = ((q : ℂ) ^ (k - 2))⁻¹ •
      ((f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ)⁻¹) ∣[k] W.alGL) := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hc : ((q : ℂ) ^ (k - 2)) ≠ 0 := zpow_ne_zero _ hqC
  set g := f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ)⁻¹ with hg
  have hS : g ∣[k] (scalarGL q)⁻¹ = ((q : ℂ) ^ (k - 2))⁻¹ • g := by
    have h1 : (g ∣[k] (scalarGL q)⁻¹) ∣[k] scalarGL q = g := by
      rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
    rw [slash_scalarGL] at h1
    calc g ∣[k] (scalarGL q)⁻¹ = ((q : ℂ) ^ (k - 2))⁻¹ • (((q : ℂ) ^ (k - 2)) • g ∣[k] (scalarGL q)⁻¹) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = ((q : ℂ) ^ (k - 2))⁻¹ • g := by rw [h1]
  rw [alGL_inv_eq, SlashAction.slash_mul, SlashAction.slash_mul, ← hg, hS, smul_slash_alGL]

end GLtools

section Factor

variable {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)

def gammaW : SL(2, ℤ) :=
  ⟨!![W.a, W.b; (W.R : ℤ), (q : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

lemma gammaW_coe : ((gammaW W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![W.a, W.b; (W.R : ℤ), (q : ℤ)] := rfl

def gamma3 : SL(2, ℤ) :=
  ⟨!![W.a, (W.R : ℤ) * W.b; 1, (q : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

lemma gamma3_coe : ((gamma3 W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![W.a, (W.R : ℤ) * W.b; 1, (q : ℤ)] := rfl

theorem alGL_eq_mapGL_mul_heckeDiag [NeZero q] :
    W.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (gammaW W) * ModularForm.heckeDiagMatrix q := by
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, gammaW_coe,
    ModularForm.val_heckeDiagMatrix (NeZero.ne q)]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] <;> ring

theorem heckeDiag_R_mul_gammaW [NeZero W.R] :
    ModularForm.heckeDiagMatrix W.R * Matrix.SpecialLinearGroup.mapGL ℝ (gammaW W) =
      Matrix.SpecialLinearGroup.mapGL ℝ (gamma3 W) * ModularForm.heckeDiagMatrix W.R := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, mapGL_coe_eq, mapGL_coe_eq, gammaW_coe, gamma3_coe,
    ModularForm.val_heckeDiagMatrix (NeZero.ne W.R)]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> ring

theorem heckeDiag_mul_heckeDiag (a b : ℕ) [NeZero a] [NeZero b] :
    ModularForm.heckeDiagMatrix a * ModularForm.heckeDiagMatrix b = ModularForm.heckeDiagMatrix (a * b) := by
  haveI : NeZero (a * b) := ⟨mul_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  apply Units.ext
  rw [Units.val_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne a), ModularForm.val_heckeDiagMatrix (NeZero.ne b),
    ModularForm.val_heckeDiagMatrix (NeZero.ne (a * b))]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def gamma4 : SL(2, ℤ) :=
  ⟨!![(q : ℤ) * W.a, (W.R : ℤ) * W.b; 1, 1], by rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

lemma gamma4_coe : ((gamma4 W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![(q : ℤ) * W.a, (W.R : ℤ) * W.b; 1, 1] := rfl

theorem heckeDiag_M_mul_gammaW_mul_heckeDiag [NeZero q] [NeZero W.R] :
    ModularForm.heckeDiagMatrix M * Matrix.SpecialLinearGroup.mapGL ℝ (gammaW W) * ModularForm.heckeDiagMatrix q =
      Matrix.SpecialLinearGroup.mapGL ℝ (gamma4 W) * scalarGL q * ModularForm.heckeDiagMatrix W.R := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [mapGL_coe_eq, mapGL_coe_eq, gammaW_coe, gamma4_coe, ModularForm.val_heckeDiagMatrix (NeZero.ne M),
    ModularForm.val_heckeDiagMatrix (NeZero.ne q), ModularForm.val_heckeDiagMatrix (NeZero.ne W.R), scalarGL_coe]
  have hM : (M : ℝ) = (q : ℝ) * (W.R : ℝ) := by exact_mod_cast W.hM
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.vecMul, dotProduct, hM] <;> ring

def frickeGL (M : ℕ) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeDiagMatrix M

theorem val_frickeGL : ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := by
  rw [frickeGL, Units.val_mul, mapGL_coe_eq, ModularGroup.coe_S, ModularForm.val_heckeDiagMatrix (NeZero.ne M)]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

end Factor

section LevelOne

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒮ℒ k]

theorem levelOne_slash_mapGL (E : F) (γ : SL(2, ℤ)) :
    (⇑E : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑E :=
  SlashInvariantFormClass.slash_action_eq E _ ⟨γ, rfl⟩

theorem levelOne_slash_mapGL_mul (E : F) (γ : SL(2, ℤ)) (X : GL (Fin 2) ℝ) :
    (⇑E : ℍ → ℂ) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) * X) = (⇑E : ℍ → ℂ) ∣[k] X := by
  rw [SlashAction.slash_mul, levelOne_slash_mapGL]

theorem levelOne_slash_heckeDiag_slash_of_mem_Gamma0 (E : F) (N : ℕ) [NeZero N]
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ((⇑E : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix N) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      (⇑E : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix N := by
  have hN : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hγ
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c, hc⟩ := hN
  let γ' : SL(2, ℤ) := ⟨!![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (N : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      c, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    rw [Matrix.det_fin_two_of]
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hc] at h
    linear_combination h⟩
  have key : ModularForm.heckeDiagMatrix N * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) * ModularForm.heckeDiagMatrix N := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, mapGL_coe_eq, mapGL_coe_eq, ModularForm.val_heckeDiagMatrix (NeZero.ne N)]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, γ', hc] <;> ring
  rw [← SlashAction.slash_mul, key, levelOne_slash_mapGL_mul]

end LevelOne

section Groups

abbrev Γ (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ GammaH M H := by
  rw [mem_GammaH_iff]
  have h0 : ModularGroup.T ∈ Gamma0 M := by rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨h0, ?_⟩
  have : gamma0Units M ⟨ModularGroup.T, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]; exact one_mem H

theorem one_mem_strictPeriods (M : ℕ) (H : Subgroup (ZMod M)ˣ) : (1 : ℝ) ∈ (Γ M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by
  rw [Subgroup.strictPeriods_SL2Z]; exact AddSubgroup.mem_zmultiples _

theorem Γ_le_SL (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Γ M H ≤ 𝒮ℒ := by
  rintro _ ⟨γ, _, rfl⟩; exact ⟨γ, rfl⟩

theorem isFiniteRelIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (N : ℕ) (H' : Subgroup (ZMod N)ˣ) :
    (Γ M H).IsFiniteRelIndex (Γ N H') := by
  haveI : (GammaH M H).FiniteIndex := inferInstance
  haveI : (Γ M H).IsArithmetic := inferInstance
  exact Subgroup.isFiniteRelIndex_of_le_right (Γ M H) (Γ_le_SL N H')

variable {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q)

theorem le_conj_SL (H : Subgroup (ZMod M)ˣ) : Γ M H ≤ ConjAct.toConjAct W.alGL⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  obtain ⟨δ, _, hW⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq W (GammaH_le_Gamma0 H hγ)
  exact ⟨δ, by rw [hW, mul_inv_cancel_right]⟩

end Groups

section Forms

variable {k : ℤ}

def restrictMF {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : ModularForm Γ₁ k) : ModularForm Γ₂ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono h)

@[scoped simp] theorem coe_restrictMF {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ ≤ Γ₁) (f : ModularForm Γ₁ k) :
    ⇑(restrictMF h f) = ⇑f := rfl

def ofCusp {Γ₁ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ₁ k) : ModularForm Γ₁ k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A hA
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f hc

@[scoped simp] theorem coe_ofCusp {Γ₁ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ₁ k) : ⇑(ofCusp f) = ⇑f := rfl

end Forms

section Eisenstein

variable {p M : ℕ} [Fact p.Prime] [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)

def wt (p : ℕ) : ℕ := 4 * (p - 1)

theorem three_le_wt : 3 ≤ wt p := by
  have := (Fact.out : p.Prime).two_le; unfold wt; omega

theorem even_wt : Even (wt p) := ⟨2 * (p - 1), by unfold wt; ring⟩

theorem sub_one_dvd_wt : p - 1 ∣ wt p := ⟨4, by unfold wt; ring⟩

theorem four_dvd_wt : 4 ∣ wt p := ⟨p - 1, rfl⟩

theorem wt_pos : 0 < wt p := lt_of_lt_of_le (by norm_num) (three_le_wt (p := p))

private def _root_.SerreFrickeCSF.E : ModularForm 𝒮ℒ (wt p) := ModularForm.E (three_le_wt (p := p))

p2m_export "SerreFrickeCSF" "E"
def Eform : ModularForm (Γ M H) (wt p) := restrictMF (Γ_le_SL M H) (E (p := p))

def EWform : ModularForm (Γ M H) (wt p) :=
  restrictMF (le_conj_SL (alDatumP hpM hpM2) H) (ModularForm.translate (E (p := p)) (alDatumP hpM hpM2).alGL)

theorem coe_Eform : ⇑(Eform (p := p) H) = ⇑(E (p := p)) := rfl

theorem coe_EWform : ⇑(EWform hpM hpM2 H) = (⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] (alDatumP hpM hpM2).alGL := rfl

theorem E_slash_W :
    (⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] (alDatumP hpM hpM2).alGL =
      (⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] ModularForm.heckeDiagMatrix p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [alGL_eq_mapGL_mul_heckeDiag, levelOne_slash_mapGL_mul]

theorem E_slash_W_inv :
    (⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] (alDatumP hpM hpM2).alGL⁻¹ =
      ((p : ℂ) ^ (((wt p : ℕ) : ℤ) - 2))⁻¹ • (⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] ModularForm.heckeDiagMatrix p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [slash_alGL_inv, ← map_inv, levelOne_slash_mapGL, E_slash_W]

def eps : ModularForm (Γ M H) (wt p) := Eform (p := p) H - (p : ℂ) • EWform hpM hpM2 H

def epsW : ModularForm (Γ M H) (wt p) :=
  ((p : ℂ) ^ (((wt p : ℕ) : ℤ) - 2))⁻¹ • EWform hpM hpM2 H - (p : ℂ) • Eform (p := p) H

theorem coe_eps : ⇑(eps hpM hpM2 H) =
    (⇑(E (p := p)) : ℍ → ℂ) - (p : ℂ) • ((⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] ModularForm.heckeDiagMatrix p) := by
  rw [eps, ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, coe_Eform, coe_EWform, E_slash_W]

theorem coe_epsW : ⇑(epsW hpM hpM2 H) =
    ((p : ℂ) ^ (((wt p : ℕ) : ℤ) - 2))⁻¹ • ((⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] ModularForm.heckeDiagMatrix p)
      - (p : ℂ) • (⇑(E (p := p)) : ℍ → ℂ) := by
  rw [epsW, ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, coe_Eform,
    coe_EWform, E_slash_W]

theorem coe_eps' : ⇑(eps hpM hpM2 H) =
    (⇑(E (p := p)) : ℍ → ℂ) - (p : ℂ) • ((⇑(E (p := p)) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] (alDatumP hpM hpM2).alGL) := by
  rw [eps, ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, coe_Eform, coe_EWform]

theorem sub_slash (k : ℤ) (A : GL (Fin 2) ℝ) (f g : ℍ → ℂ) : (f - g) ∣[k] A = f ∣[k] A - g ∣[k] A := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

theorem smul_slash_alGL_inv {M' q' : ℕ} [NeZero M'] (W : ModularForm.AtkinLehnerDatum M' q') (k : ℤ) (c : ℂ)
    (f : ℍ → ℂ) : (c • f) ∣[k] W.alGL⁻¹ = c • (f ∣[k] W.alGL⁻¹) := by
  rw [ModularForm.smul_slash]
  congr 1
  rw [UpperHalfPlane.σ, if_pos]; · rfl
  rw [map_inv, Units.val_inv_eq_inv_val, W.val_det_alGL]
  exact inv_pos.mpr (by exact_mod_cast W.q_pos)

theorem coe_epsW_eq_slash :
    ⇑(epsW hpM hpM2 H) = (⇑(eps hpM hpM2 H) : ℍ → ℂ) ∣[((wt p : ℕ) : ℤ)] (alDatumP hpM hpM2).alGL⁻¹ := by
  rw [coe_epsW, coe_eps', sub_slash, smul_slash_alGL_inv, ← SlashAction.slash_mul, mul_inv_cancel,
    SlashAction.slash_one, E_slash_W_inv]

end Eisenstein

section ATransforms

variable {p M : ℕ} [Fact p.Prime] [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
  [NeZero (M / p)] (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (σe : SL(2, ℤ)) (hσe : σe ∈ Gamma0 M)

set_option quotPrecheck false in
local notation "𝕎" => alDatumP hpM hpM2
set_option quotPrecheck false in
local notation "𝔸" => ((Matrix.SpecialLinearGroup.mapGL ℝ σe : GL (Fin 2) ℝ) * Wd.alGL)
set_option quotPrecheck false in
local notation "𝔼" => ((E (p := p) : ModularForm 𝒮ℒ (wt p)) : ℍ → ℂ)
local notation "𝕒" => (((wt p : ℕ) : ℤ))
local notation "D" => ModularForm.heckeDiagMatrix

include hpM in
theorem Rd_eq : Wd.R = p := by
  have h1 : M = (M / p) * p := (Nat.div_mul_cancel hpM).symm
  have h2 : (M / p) * Wd.R = (M / p) * p := by rw [← Wd.hM]; exact h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne (M / p))) h2

scoped instance neZero_p : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

include hpM in
theorem heckeDiag_p_mul_Q : D p * D (M / p) = D M := by
  rw [heckeDiag_mul_heckeDiag]; congr 1; exact (M_eq hpM).symm

include hpM in
theorem heckeDiag_Q_mul_p : D (M / p) * D p = D M := by
  rw [heckeDiag_mul_heckeDiag]; congr 1; rw [mul_comm]; exact (M_eq hpM).symm

theorem E_slash_A : 𝔼 ∣[𝕒] 𝔸 = 𝔼 ∣[𝕒] D (M / p) := by
  rw [levelOne_slash_mapGL_mul, alGL_eq_mapGL_mul_heckeDiag Wd, levelOne_slash_mapGL_mul]

include hpM hσe in

theorem E_slash_W_slash_A : (𝔼 ∣[𝕒] (𝕎).alGL) ∣[𝕒] 𝔸 = 𝔼 ∣[𝕒] D M := by
  haveI : NeZero Wd.R := ⟨by rw [Rd_eq hpM Wd]; exact NeZero.ne p⟩
  obtain ⟨δ, _, hδ⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq (𝕎) hσe
  rw [← SlashAction.slash_mul, ← mul_assoc, hδ, mul_assoc, levelOne_slash_mapGL_mul, alGL_eq_mapGL_mul_heckeDiag (𝕎),
    mul_assoc, levelOne_slash_mapGL_mul, alGL_eq_mapGL_mul_heckeDiag Wd, ← mul_assoc,
    show D p = D Wd.R by rw [Rd_eq hpM Wd], heckeDiag_R_mul_gammaW Wd, mul_assoc, levelOne_slash_mapGL_mul,
    Rd_eq hpM Wd, heckeDiag_p_mul_Q hpM]

theorem sqUnit_inv_mem_Gamma0_Q : (𝕎).sqUnitSL⁻¹ ∈ Gamma0 (M / p) := by
  have h := (Gamma0 M).inv_mem (𝕎).sqUnitSL_mem
  rw [Gamma0_mem] at h ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
  exact (Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd hpM)).trans h

theorem E_slash_DQ_slash_W_inv :
    (𝔼 ∣[𝕒] D (M / p)) ∣[𝕒] (𝕎).alGL⁻¹ = ((p : ℂ) ^ (𝕒 - 2))⁻¹ • 𝔼 ∣[𝕒] D M := by
  haveI : NeZero (𝕎).R := ‹NeZero (M / p)›
  rw [slash_alGL_inv, ← map_inv, levelOne_slash_heckeDiag_slash_of_mem_Gamma0 _ _ (sqUnit_inv_mem_Gamma0_Q hpM hpM2),
    alGL_eq_mapGL_mul_heckeDiag (𝕎), ← SlashAction.slash_mul, ← mul_assoc]
  have h := heckeDiag_R_mul_gammaW (𝕎)
  rw [show (𝕎).R = M / p from rfl] at h
  rw [h, mul_assoc, levelOne_slash_mapGL_mul, heckeDiag_Q_mul_p hpM]

theorem E_slash_DM_slash_W_inv : (𝔼 ∣[𝕒] D M) ∣[𝕒] (𝕎).alGL⁻¹ = 𝔼 ∣[𝕒] D (M / p) := by
  haveI : NeZero (𝕎).R := ‹NeZero (M / p)›
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [slash_alGL_inv, ← map_inv,
    levelOne_slash_heckeDiag_slash_of_mem_Gamma0 _ _ ((Gamma0 M).inv_mem (𝕎).sqUnitSL_mem),
    alGL_eq_mapGL_mul_heckeDiag (𝕎), ← SlashAction.slash_mul, ← mul_assoc]
  have h := heckeDiag_M_mul_gammaW_mul_heckeDiag (𝕎)
  rw [show (𝕎).R = M / p from rfl] at h
  rw [h, mul_assoc, levelOne_slash_mapGL_mul, SlashAction.slash_mul, slash_scalarGL, ModularForm.smul_slash,
    ModularForm.σ_heckeDiagMatrix, smul_smul]
  simp only [ContinuousAlgEquiv.refl_apply]
  rw [inv_mul_cancel₀ (zpow_ne_zero _ hpC), one_smul]

theorem det_A_pos : 0 < ((Matrix.GeneralLinearGroup.det (𝔸) : ℝˣ) : ℝ) := by
  rw [map_mul, Units.val_mul, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, one_mul]
  exact Wd.det_alGL_pos

theorem smul_slash_A (k : ℤ) (c : ℂ) (f : ℍ → ℂ) : (c • f) ∣[k] 𝔸 = c • (f ∣[k] 𝔸) := by
  rw [ModularForm.smul_slash]; congr 1
  rw [UpperHalfPlane.σ, if_pos (det_A_pos Wd σe)]; rfl

def epsA (EA EWA : ModularForm (Γ M H) (wt p)) : ModularForm (Γ M H) (wt p) := EA - (p : ℂ) • EWA

def epsAW (EA EWA : ModularForm (Γ M H) (wt p)) : ModularForm (Γ M H) (wt p) :=
  ((p : ℂ) ^ (𝕒 - 2))⁻¹ • EWA - (p : ℂ) • EA

include hpM hσe in
theorem coe_epsA (EA EWA : ModularForm (Γ M H) (wt p))
    (hEA : ⇑EA = 𝔼 ∣[𝕒] 𝔸) (hEWA : ⇑EWA = (𝔼 ∣[𝕒] (𝕎).alGL) ∣[𝕒] 𝔸) :
    ⇑(epsA (p := p) H EA EWA) = 𝔼 ∣[𝕒] D (M / p) - (p : ℂ) • 𝔼 ∣[𝕒] D M := by
  rw [epsA, ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, hEA, hEWA, E_slash_A, E_slash_W_slash_A hpM hpM2 Wd σe hσe]

include hpM hσe in
theorem coe_epsAW (EA EWA : ModularForm (Γ M H) (wt p))
    (hEA : ⇑EA = 𝔼 ∣[𝕒] 𝔸) (hEWA : ⇑EWA = (𝔼 ∣[𝕒] (𝕎).alGL) ∣[𝕒] 𝔸) :
    ⇑(epsAW (p := p) H EA EWA) = ((p : ℂ) ^ (𝕒 - 2))⁻¹ • 𝔼 ∣[𝕒] D M - (p : ℂ) • 𝔼 ∣[𝕒] D (M / p) := by
  rw [epsAW, ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, hEA, hEWA, E_slash_A,
    E_slash_W_slash_A hpM hpM2 Wd σe hσe]

theorem coe_epsA_eq_slash (EA EWA : ModularForm (Γ M H) (wt p))
    (hEA : ⇑EA = 𝔼 ∣[𝕒] 𝔸) (hEWA : ⇑EWA = (𝔼 ∣[𝕒] (𝕎).alGL) ∣[𝕒] 𝔸) :
    ⇑(epsA (p := p) H EA EWA) = (⇑(eps hpM hpM2 H) : ℍ → ℂ) ∣[𝕒] 𝔸 := by
  rw [epsA, ModularForm.coe_sub, ModularForm.IsGLPos.coe_smul, hEA, hEWA, coe_eps', sub_slash, smul_slash_A]

include hσe in

theorem coe_epsAW_eq_slash (EA EWA : ModularForm (Γ M H) (wt p))
    (hEA : ⇑EA = 𝔼 ∣[𝕒] 𝔸) (hEWA : ⇑EWA = (𝔼 ∣[𝕒] (𝕎).alGL) ∣[𝕒] 𝔸) :
    ⇑(epsAW (p := p) H EA EWA) = (⇑(epsA (p := p) H EA EWA) : ℍ → ℂ) ∣[𝕒] (𝕎).alGL⁻¹ := by
  rw [coe_epsAW hpM hpM2 H Wd σe hσe EA EWA hEA hEWA, coe_epsA hpM hpM2 H Wd σe hσe EA EWA hEA hEWA, sub_slash,
    smul_slash_alGL_inv, E_slash_DQ_slash_W_inv, E_slash_DM_slash_W_inv]

lemma coe_S_inv : ((ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S]; simp [Matrix.adjugate_fin_two]

def rho0 : SL(2, ℤ) := gammaW Wd * gamma3 (𝕎) * ModularGroup.S⁻¹

theorem Wd_mul_W : Wd.alGL * (𝕎).alGL = Matrix.SpecialLinearGroup.mapGL ℝ (rho0 hpM hpM2 Wd) * frickeGL M := by
  haveI : NeZero (𝕎).R := ‹NeZero (M / p)›
  have h := heckeDiag_R_mul_gammaW (𝕎)
  rw [show (𝕎).R = M / p from rfl] at h
  rw [alGL_eq_mapGL_mul_heckeDiag Wd, alGL_eq_mapGL_mul_heckeDiag (𝕎), rho0, frickeGL, map_mul, map_mul, map_inv]
  calc Matrix.SpecialLinearGroup.mapGL ℝ (gammaW Wd) * D (M / p) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (gammaW (𝕎)) * D p)
      = Matrix.SpecialLinearGroup.mapGL ℝ (gammaW Wd) * (D (M / p) * Matrix.SpecialLinearGroup.mapGL ℝ (gammaW (𝕎))) * D p := by
        group
    _ = Matrix.SpecialLinearGroup.mapGL ℝ (gammaW Wd) * Matrix.SpecialLinearGroup.mapGL ℝ (gamma3 (𝕎)) * (D (M / p) * D p) := by
        rw [h]; group
    _ = _ := by rw [heckeDiag_Q_mul_p hpM]; group

include hpM in

theorem rho0_mem : rho0 hpM hpM2 Wd ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have h10 : ((rho0 hpM hpM2 Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      -(((M / p : ℕ) : ℤ) * ((Wd.R : ℤ) * (𝕎).b + (p : ℤ))) := by
    rw [rho0, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, gammaW_coe, gamma3_coe, coe_S_inv]
    simp [Matrix.mul_apply, Fin.sum_univ_two, show ((𝕎).R : ℤ) = ((M / p : ℕ) : ℤ) from rfl]
    ring
  show (((rho0 hpM hpM2 Wd : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod M) = 0
  rw [h10, Rd_eq hpM Wd]
  have hM : ((M / p : ℕ) : ZMod M) * ((p : ℕ) : ZMod M) = 0 := by
    rw [← Nat.cast_mul, mul_comm, ← M_eq hpM, ZMod.natCast_self]
  simp only [Int.cast_neg, Int.cast_mul, Int.cast_add, Int.cast_natCast]
  linear_combination (-(((𝕎).b : ℤ) : ZMod M) - 1) * hM

end ATransforms

section Expansions

variable {p : ℕ} [Fact p.Prime]

set_option quotPrecheck false in
local notation "𝔼" => ((E (p := p) : ModularForm 𝒮ℒ (wt p)) : ℍ → ℂ)
local notation "𝕒" => (((wt p : ℕ) : ℤ))
local notation "D" => ModularForm.heckeDiagMatrix

theorem E_def : E (p := p) = ModularForm.E (three_le_wt (p := p)) := rfl

lemma sigma_one : (ArithmeticFunction.sigma (wt p - 1)) 1 = 1 := by
  simp [ArithmeticFunction.sigma_apply]

theorem exists_PE : ∃ (x : ℤ) (s : ℕ), ¬ p ∣ s ∧ (p : ℤ) ∣ x ∧
    ∀ n : ℕ, (((if n = 0 then (s : ℤ) else x * ((ArithmeticFunction.sigma (wt p - 1)) n : ℤ)) : ℤ) : ℂ) =
      (s : ℂ) * PowerSeries.coeff n (qExpansion 1 𝔼) := by
  obtain ⟨x, s, hps, hx, hpx⟩ :=
    ModularForm.eisenstein_qCoeff_p_integral_dvd p (three_le_wt (p := p)) even_wt sub_one_dvd_wt 1 one_pos
  refine ⟨x, s, hps, hpx, fun n => ?_⟩
  have hE := EisensteinSeries.E_qExpansion_coeff (three_le_wt (p := p)) even_wt
  rw [E_def]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [hE 0]; simp
  · rw [if_neg hn, hE n, if_neg hn]
    rw [hE 1, if_neg one_ne_zero, sigma_one] at hx
    push_cast
    rw [hx]; push_cast; ring

def xE : ℤ := (exists_PE (p := p)).choose
def sE : ℕ := (exists_PE (p := p)).choose_spec.choose

theorem not_p_dvd_sE : ¬ p ∣ sE (p := p) := (exists_PE (p := p)).choose_spec.choose_spec.1
theorem p_dvd_xE : (p : ℤ) ∣ xE (p := p) := (exists_PE (p := p)).choose_spec.choose_spec.2.1

def Psig : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 0 else ((ArithmeticFunction.sigma (wt p - 1)) n : ℤ)

def PE : PowerSeries ℤ := PowerSeries.C (sE (p := p) : ℤ) + PowerSeries.C (xE (p := p)) * Psig (p := p)

theorem coeff_PE (n : ℕ) : PowerSeries.coeff n (PE (p := p)) =
    if n = 0 then (sE (p := p) : ℤ) else xE (p := p) * ((ArithmeticFunction.sigma (wt p - 1)) n : ℤ) := by
  rw [PE, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, Psig, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem PE_map : (PE (p := p)).map (Int.castRingHom ℂ) = (sE (p := p) : ℂ) • qExpansion 1 𝔼 := by
  ext n
  rw [PowerSeries.coeff_map, coeff_PE, PowerSeries.coeff_smul, smul_eq_mul, eq_intCast]
  exact (exists_PE (p := p)).choose_spec.choose_spec.2.2 n

theorem heckeV_C {R : Type*} [CommRing R] (N : ℕ) (hN : N ≠ 0) (c : R) :
    PowerSeries.heckeV N (PowerSeries.C c) = PowerSeries.C c := by
  ext n
  rw [PowerSeries.coeff_heckeV, PowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases h : N ∣ n
  · rw [if_pos h]
    obtain ⟨c', rfl⟩ := h
    rcases eq_or_ne c' 0 with rfl | hc'
    · simp
    · rw [if_neg (by rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hN)]; exact hc'),
        if_neg (mul_ne_zero hN hc')]
  · rw [if_neg h, if_neg]; rintro rfl; exact h (dvd_zero N)

theorem map_heckeV {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (P : PowerSeries R) :
    (PowerSeries.heckeV N P).map f = PowerSeries.heckeV N (P.map f) := by
  ext n; simp only [PowerSeries.coeff_map, PowerSeries.coeff_heckeV]; split_ifs <;> simp

theorem heckeV_PE (N : ℕ) (hN : N ≠ 0) : PowerSeries.heckeV N (PE (p := p)) =
    PowerSeries.C (sE (p := p) : ℤ) + PowerSeries.C (xE (p := p)) * PowerSeries.heckeV N (Psig (p := p)) := by
  rw [PE, map_add, heckeV_C N hN, ← PowerSeries.smul_eq_C_mul, ← PowerSeries.smul_eq_C_mul, LinearMap.map_smul]

theorem qExpansion_E_slash_heckeDiag {Γ₁ : Subgroup (GL (Fin 2) ℝ)} (h1 : (1 : ℝ) ∈ Γ₁.strictPeriods)
    (N : ℕ) (hN : N ≠ 0) (X : ModularForm Γ₁ (wt p)) (hX : ⇑X = 𝔼 ∣[𝕒] D N) :
    (sE (p := p) : ℂ) • qExpansion 1 ⇑X =
      ((N : ℂ) ^ (wt p - 1)) • (PowerSeries.heckeV N (PE (p := p))).map (Int.castRingHom ℂ) := by
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  set φ : ℍ → ℂ := fun τ => (E (p := p)) (D N • τ) with hφ
  have hpow : ((N : ℂ) ^ (𝕒 - 1)) = (N : ℂ) ^ (wt p - 1) := by
    have : (𝕒 - 1) = ((wt p - 1 : ℕ) : ℤ) := by
      have := wt_pos (p := p); omega
    rw [this, zpow_natCast]
  have hXφ : ⇑X = ((N : ℂ) ^ (wt p - 1)) • φ := by
    rw [hX]; funext τ
    rw [ModularForm.slash_heckeDiagMatrix_apply _ hN, Pi.smul_apply, smul_eq_mul, hpow]
  have hanX : AnalyticAt ℂ (cuspFunction 1 ⇑X) 0 := ModularFormClass.analyticAt_cuspFunction_zero X one_pos h1
  have hφX : φ = (((N : ℂ) ^ (wt p - 1))⁻¹) • ⇑X := by
    rw [hXφ, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hNC), one_smul]
  have hanφ : AnalyticAt ℂ (cuspFunction 1 φ) 0 := by
    rw [hφX, cuspFunction_smul hanX.continuousAt]
    exact hanX.const_smul
  rw [hXφ, UpperHalfPlane.qExpansion_smul hanφ, smul_comm]
  congr 1
  ext n
  rw [PowerSeries.coeff_smul, PowerSeries.coeff_map, PowerSeries.coeff_heckeV, smul_eq_mul]
  have hq := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul (E (p := p)) one_mem_strictPeriods_SL hN n
  simp only [ModularFormClass.qCoeff] at hq
  change (sE (p := p) : ℂ) * PowerSeries.coeff n (qExpansion 1 φ) = _
  rw [hq]
  have hc := fun m => congrArg (PowerSeries.coeff m) (PE_map (p := p))
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_smul, smul_eq_mul] at hc
  split_ifs with hdvd
  · rw [← hc, eq_intCast]
  · simp

end Expansions

section Helpers

theorem real_smul_fun (r : ℝ) (f : ℍ → ℂ) : r • f = ((r : ℂ)) • f := by
  funext τ; simp [Pi.smul_apply, Complex.real_smul]

theorem mul_pow_slash (k₁ k₂ : ℤ) (A : GL (Fin 2) ℝ) (g ε : ℍ → ℂ) (i : ℕ) :
    (g * ε ^ i) ∣[k₁ + (i : ℤ) * k₂] A =
      (((|((Matrix.GeneralLinearGroup.det A : ℝˣ) : ℝ)| : ℝ) : ℂ) ^ i) • ((g ∣[k₁] A) * (ε ∣[k₂] A) ^ i) := by
  have hprod : ε ^ i = ∏ _j ∈ Finset.range i, ε := by rw [Finset.prod_const, Finset.card_range]
  have hpow : (ε ^ i) ∣[(i : ℤ) * k₂] A =
      ((|((Matrix.GeneralLinearGroup.det A : ℝˣ) : ℝ)| : ℝ) ^ ((i : ℤ) - 1)) • ∏ _j ∈ Finset.range i, (ε ∣[k₂] A) := by
    have h := @ModularForm.prod_slash ℕ k₂ A (fun _ => ε) (Finset.range i)
    rw [Finset.card_range] at h
    rw [hprod, mul_comm ((i : ℤ)) k₂, h]
  rw [ModularForm.mul_slash, hpow, Finset.prod_const, Finset.card_range]
  set d : ℝ := |((Matrix.GeneralLinearGroup.det A : ℝˣ) : ℝ)| with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact abs_ne_zero.mpr (Units.ne_zero _)
  rw [real_smul_fun, real_smul_fun]
  have hz : ((d ^ ((i : ℤ) - 1) : ℝ) : ℂ) = (d : ℂ) ^ ((i : ℤ) - 1) := by push_cast; rfl
  rw [hz]
  ext τ
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.pow_apply]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  have : (d : ℂ) * (d : ℂ) ^ ((i : ℤ) - 1) = (d : ℂ) ^ i := by
    rw [← zpow_natCast, ← zpow_one_add₀ hdC]; congr 1; ring
  calc (d : ℂ) * ((g ∣[k₁] A) τ * ((d : ℂ) ^ ((i : ℤ) - 1) * ((ε ∣[k₂] A) ^ i) τ))
      = ((d : ℂ) * (d : ℂ) ^ ((i : ℤ) - 1)) * ((g ∣[k₁] A) τ * ((ε ∣[k₂] A) ^ i) τ) := by ring
    _ = (d : ℂ) ^ i * ((g ∣[k₁] A) τ * ((ε ∣[k₂] A) τ) ^ i) := by rw [this]; rfl

theorem slash_congr_weight {k k' : ℤ} (h : k = k') (f : ℍ → ℂ) (A : GL (Fin 2) ℝ) : f ∣[k] A = f ∣[k'] A := by
  subst h; rfl

theorem exists_intSeries_of_forall_mem_bot (g : ℍ → ℂ)
    (h : ∀ n : ℕ, ModularFormClass.qCoeff g n ∈ (⊥ : Subring ℂ)) :
    ∃ P : PowerSeries ℤ, P.map (Int.castRingHom ℂ) = qExpansion 1 g := by
  choose m hm using fun n => Subring.mem_bot.mp (h n)
  refine ⟨PowerSeries.mk m, ?_⟩
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
  exact hm n

theorem Gamma1_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma1 M ≤ GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := (Gamma1_mem M A).mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2
  refine ⟨h0, ?_⟩
  have : gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.1, Units.val_one]
  rw [this]; exact one_mem H

theorem map_map_int (P : PowerSeries ℤ) :
    (P.map (Int.castRingHom ↥(integralClosure ℤ ℂ))).map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      P.map (Int.castRingHom ℂ) := by
  ext n; simp [PowerSeries.coeff_map]

theorem map_map_int_quot (P : PowerSeries ℤ) (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) :
    (P.map (Int.castRingHom ↥(integralClosure ℤ ℂ))).map (Ideal.Quotient.mk 𝔪) =
      P.map ((Ideal.Quotient.mk 𝔪).comp (Int.castRingHom ↥(integralClosure ℤ ℂ))) := by
  ext n; simp [PowerSeries.coeff_map]

end Helpers

section MainProof

set_option maxHeartbeats 4000000 in
theorem main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (_h𝔪 : 𝔪.IsPrime)
    (hp𝔪 : ((p : ℕ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp ⇑f pf)
    (Dn : ℕ) (hD : ¬ p ∣ Dn)
    (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((Dn : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    ∃ (w : ℕ) (G : ModularForm (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℤ) + w))
      (P : PowerSeries ℤ) (D₁ D₂ : ℕ) (PGW : PowerSeries ↥(integralClosure ℤ ℂ)),
      0 < w ∧ (p - 1 ∣ w) ∧ (4 ∣ w) ∧ ¬ p ∣ D₁ ∧ ¬ p ∣ D₂ ∧
      ModularCurve.IsIntegralQExp ⇑G P ∧
      (∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n P - (D₁ : ℤ) * PowerSeries.coeff n pf) ∧
      PGW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((D₂ : ℂ) • ((⇑G : UpperHalfPlane → ℂ) ∣[(2 : ℤ) + w] WQ)) ∧
      (∀ n : ℕ, ((Dn : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n PGW -
          ((D₂ * D₁ * (M / p) ^ w : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n pfW ∈ 𝔪) := by

  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  have hQ0 : (M / p) ≠ 0 := NeZero.ne _
  have hQC : ((M / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hQ0
  set W : ModularForm.AtkinLehnerDatum M p := alDatumP hpM hpM2 with hWdef
  have hHpW : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H := hHp
  have hHpd : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro Wd.R Wd.hM.symm) u = 1 → u ∈ H := hHp
  set H' : Subgroup (ZMod (M / p))ˣ := H.map (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)) with hH'
  haveI hfi₁ : (Γ M H).IsFiniteRelIndex (Γ (M / p) H') := isFiniteRelIndex M H (M / p) H'
  haveI hfi₂ : (Γ M H).IsFiniteRelIndex (Γ (M / p) (ModularCurve.infSubgroup p M H hpM)) := hfi₁
  haveI hfi₃ : (Γ M H).IsFiniteRelIndex (Γ W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) := hfi₁
  have h1Γ : (1 : ℝ) ∈ (Γ M H).strictPeriods := one_mem_strictPeriods M H
  obtain ⟨⟨σe, hσe⟩, hσee⟩ := CohCarrier.gamma0Units_surjective M e
  have hstD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2
  set A : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ σe : GL (Fin 2) ℝ) * Wd.alGL with hAdef
  set u : SL(2, ℤ) := W.sqUnitSL with hudef
  have hu_inv : u⁻¹ ∈ Gamma0 M := (Gamma0 M).inv_mem W.sqUnitSL_mem
  set d₀ : (ZMod M)ˣ := gamma0Units M ⟨u⁻¹, hu_inv⟩ with hd₀

  set a : ℕ := wt p with hadef
  have ha1 : 1 ≤ a := Nat.succ_le_of_lt (wt_pos (p := p))
  set s : ℕ := sE (p := p) with hsdef
  set x : ℤ := xE (p := p) with hxdef
  have hps : ¬ p ∣ s := not_p_dvd_sE
  obtain ⟨x', hx'⟩ : (p : ℤ) ∣ x := p_dvd_xE
  have hsC : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := fun h => hps (h ▸ dvd_zero p)
    exact_mod_cast this

  have hint : ∀ d : (ZMod M)ˣ, (∀ n, ModularFormClass.qCoeff (⇑(CuspForm.diamondLinH 2 d f)) n ∈ (⊥ : Subring ℂ)) ∧
      (∀ n, ModularFormClass.qCoeff (ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 d f)) n ∈ (⊥ : Subring ℂ)) := by
    intro d
    have ht : (CuspForm.diamondLinH 2 d : CuspForm (Γ M H) 2 →ₗ[ℂ] CuspForm (Γ M H) 2) ∈ CuspForm.heckeRingH M H 2 :=
      CuspForm.heckeGenH_mem_heckeRingH ∅ 2 (CohCarrier.Gen.dia d)
    exact ⟨fun n => (hf _ ht W n).1, fun n => (hf _ ht W n).2⟩

  set fM : ModularForm (Γ M H) 2 := ofCusp f with hfM
  have hcoe_diam : ∀ (F : CuspForm (Γ M H) 2), ⇑(CuspForm.diamondLinH 2 d₀ F) =
      ⇑F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (u⁻¹) : GL (Fin 2) ℝ) := fun F =>
    CuspForm.coe_diamondLinH_eq_slash 2 hstD d₀ ⟨u⁻¹, hu_inv⟩ rfl F
  have hslashW_inv : ∀ (F : CuspForm (Γ M H) 2),
      (⇑F : ℍ → ℂ) ∣[(2 : ℤ)] W.alGL⁻¹ = ModularForm.alSlash W 2 ⇑(CuspForm.diamondLinH 2 d₀ F) := by
    intro F
    rw [slash_alGL_inv, ModularForm.alSlash_def, hcoe_diam, map_inv, sub_self, zpow_zero, inv_one, one_smul]
  obtain ⟨X₀, hX₀⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHpW 2 (CuspForm.diamondLinH 2 d₀ f)
  set fW : ModularForm (Γ M H) 2 := ofCusp X₀ with hfWdef
  have hfW : ⇑fW = ⇑fM ∣[(2 : ℤ)] W.alGL⁻¹ := by
    rw [hfWdef, coe_ofCusp, hX₀, hfM, coe_ofCusp, hslashW_inv]
  obtain ⟨Xe, hXe⟩ := CuspForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one Wd H hHpd 2
    (CuspForm.diamondLinH 2 e f)
  have hXeA : ⇑Xe = ⇑f ∣[(2 : ℤ)] A := by
    rw [hXe, ModularForm.alSlash_def, CuspForm.coe_diamondLinH_eq_slash 2 hstD e ⟨σe, hσe⟩ hσee f, hAdef,
      SlashAction.slash_mul]
  set gA : ModularForm (Γ M H) 2 := ofCusp Xe with hgAdef
  obtain ⟨Y, hY⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHpW 2 (CuspForm.diamondLinH 2 d₀ Xe)
  set gAW : ModularForm (Γ M H) 2 := ofCusp Y with hgAWdef
  have hgAW : ⇑gAW = ⇑gA ∣[(2 : ℤ)] W.alGL⁻¹ := by
    rw [hgAWdef, coe_ofCusp, hY, hgAdef, coe_ofCusp, hslashW_inv]

  obtain ⟨δ', hδ', hWdu⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq Wd hu_inv
  set ρ : SL(2, ℤ) := σe * δ' * rho0 hpM hpM2 Wd with hρ
  have hρ0 : ρ ∈ Gamma0 M := (Gamma0 M).mul_mem ((Gamma0 M).mul_mem hσe hδ') (rho0_mem hpM hpM2 Wd)
  set d₁ : (ZMod M)ˣ := gamma0Units M ⟨ρ, hρ0⟩ with hd₁
  have hmat : (Matrix.SpecialLinearGroup.mapGL ℝ σe : GL (Fin 2) ℝ) * Wd.alGL *
      (Matrix.SpecialLinearGroup.mapGL ℝ (u⁻¹) : GL (Fin 2) ℝ) * W.alGL =
      (Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ) * frickeGL M := by
    calc (Matrix.SpecialLinearGroup.mapGL ℝ σe : GL (Fin 2) ℝ) * Wd.alGL *
          (Matrix.SpecialLinearGroup.mapGL ℝ (u⁻¹) : GL (Fin 2) ℝ) * W.alGL
        = (Matrix.SpecialLinearGroup.mapGL ℝ σe : GL (Fin 2) ℝ) *
            (Wd.alGL * (Matrix.SpecialLinearGroup.mapGL ℝ (u⁻¹) : GL (Fin 2) ℝ)) * W.alGL := by group
      _ = (Matrix.SpecialLinearGroup.mapGL ℝ σe : GL (Fin 2) ℝ) * (Matrix.SpecialLinearGroup.mapGL ℝ δ') *
            (Wd.alGL * W.alGL) := by rw [hWdu]; group
      _ = _ := by rw [Wd_mul_W hpM hpM2 Wd, hρ, map_mul, map_mul]; group
  have hYcoe : ⇑Y = (⇑(CuspForm.diamondLinH 2 d₁ f) : ℍ → ℂ) ∣[(2 : ℤ)] frickeGL M := by
    rw [hY, ModularForm.alSlash_def, hcoe_diam, hXeA, hAdef, CuspForm.coe_diamondLinH_eq_slash 2 hstD d₁ ⟨ρ, hρ0⟩ rfl f]
    simp only [← SlashAction.slash_mul]
    rw [hmat]
  set f₁ : ModularForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2 :=
    restrictMF (Subgroup.map_mono (Gamma1_le_GammaH M H)) (ofCusp (CuspForm.diamondLinH 2 d₁ f)) with hf₁
  obtain ⟨Pd₁, hPd₁⟩ := exists_intSeries_of_forall_mem_bot _ (hint d₁).1
  have hf₁int : ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ 0 * PowerSeries.coeff n (qExpansion 1 (⇑f₁ : ℍ → ℂ))) := by
    intro n
    rw [pow_zero, one_mul, hf₁, coe_restrictMF, coe_ofCusp, ← hPd₁, PowerSeries.coeff_map]
    exact ⟨Polynomial.X - Polynomial.C (PowerSeries.coeff n Pd₁), Polynomial.monic_X_sub_C _, by simp⟩
  obtain ⟨b, hb⟩ := ModularCurve.exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff M f₁ 0 hf₁int
    (frickeGL M) val_frickeGL
  have hbY : ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ b * PowerSeries.coeff n (qExpansion 1 (⇑Y : ℍ → ℂ))) := by
    intro n; rw [hYcoe]; exact hb n

  set i : ℕ := b + 1 with hidef
  have hi1 : 1 ≤ i := Nat.le_add_left 1 b
  set ε : ModularForm (Γ M H) a := eps hpM hpM2 H with hεdef
  set εW : ModularForm (Γ M H) a := epsW hpM hpM2 H with hεWdef
  have hεW : ⇑εW = ⇑ε ∣[(a : ℤ)] W.alGL⁻¹ := coe_epsW_eq_slash hpM hpM2 H
  set F : ModularForm (Γ M H) (2 + (i : ℤ) * (a : ℤ)) := fM.mul (ε.pow i) with hFdef
  obtain ⟨EA, hEA, -⟩ := ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace p M H hpM hHp Wd e he
    σe hσe hσee WQ hWQ (Eform (p := p) H)
  obtain ⟨EWA, hEWA, -⟩ := ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace p M H hpM hHp Wd
    e he σe hσe hσee WQ hWQ (EWform hpM hpM2 H)
  rw [coe_Eform] at hEA
  rw [coe_EWform] at hEWA
  obtain ⟨F', hF', htr⟩ := ModularForm.exists_coe_eq_slash_mul_alGL_and_coe_trace_slash_eq_coe_trace p M H hpM hHp Wd
    e he σe hσe hσee WQ hWQ F
  set ε'' : ModularForm (Γ M H) a := epsA (p := p) H EA EWA with hε''
  set εW'' : ModularForm (Γ M H) a := epsAW (p := p) H EA EWA with hεW''def
  have hεW'' : ⇑εW'' = ⇑ε'' ∣[(a : ℤ)] W.alGL⁻¹ := coe_epsAW_eq_slash hpM hpM2 H Wd σe hσe EA EWA hEA hEWA
  set g'' : ModularForm (Γ M H) 2 := (((M / p : ℕ) : ℂ) ^ i) • gA with hg''
  set gW'' : ModularForm (Γ M H) 2 := (((M / p : ℕ) : ℂ) ^ i) • gAW with hgW''
  have hgW''slash : ⇑gW'' = ⇑g'' ∣[(2 : ℤ)] W.alGL⁻¹ := by
    rw [hgW'', hg'', ModularForm.IsGLPos.coe_smul, ModularForm.IsGLPos.coe_smul, smul_slash_alGL_inv, hgAW]
  have hdetA : (((|((Matrix.GeneralLinearGroup.det A : ℝˣ) : ℝ)| : ℝ) : ℂ)) = ((M / p : ℕ) : ℂ) := by
    rw [hAdef, map_mul, Units.val_mul, Matrix.SpecialLinearGroup.det_mapGL, Units.val_one, one_mul, Wd.val_det_alGL,
      abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast; rfl
  have hFF : F' = g''.mul (ε''.pow i) := by
    apply DFunLike.ext'
    rw [hF', hFdef, hfM, hg'', hgAdef, hε'']
    simp only [ModularForm.coe_mul, ModularForm.coe_pow, ModularForm.IsGLPos.coe_smul, coe_ofCusp]
    rw [mul_pow_slash, hdetA, hXeA, coe_epsA_eq_slash hpM hpM2 H Wd σe EA EWA hEA hEWA, smul_mul_assoc, hAdef]

  set ιℂ : ℤ →+* ℂ := Int.castRingHom ℂ with hιℂ
  set PEz : PowerSeries ℤ := PE (p := p) with hPEz
  set Pσ : PowerSeries ℤ := Psig (p := p) with hPσ
  have hPEmap : PEz.map ιℂ = (s : ℂ) • qExpansion 1 (⇑(E (p := p)) : ℍ → ℂ) := PE_map
  have hqE : (s : ℂ) • qExpansion 1 (⇑(Eform (p := p) H) : ℍ → ℂ) = PEz.map ιℂ := by rw [coe_Eform, hPEmap]
  have hqEW : (s : ℂ) • qExpansion 1 (⇑(EWform hpM hpM2 H) : ℍ → ℂ) =
      ((p : ℂ) ^ (a - 1)) • (PowerSeries.heckeV p PEz).map ιℂ :=
    qExpansion_E_slash_heckeDiag h1Γ p hp0 _ ((coe_EWform hpM hpM2 H).trans (E_slash_W hpM hpM2))
  have hqEA : (s : ℂ) • qExpansion 1 (⇑EA : ℍ → ℂ) =
      (((M / p : ℕ) : ℂ) ^ (a - 1)) • (PowerSeries.heckeV (M / p) PEz).map ιℂ :=
    qExpansion_E_slash_heckeDiag h1Γ (M / p) hQ0 _ (hEA.trans (E_slash_A Wd σe))
  have hqEWA : (s : ℂ) • qExpansion 1 (⇑EWA : ℍ → ℂ) =
      ((M : ℂ) ^ (a - 1)) • (PowerSeries.heckeV M PEz).map ιℂ :=
    qExpansion_E_slash_heckeDiag h1Γ M (NeZero.ne M) _ (hEWA.trans (E_slash_W_slash_A hpM hpM2 Wd σe hσe))

  have hVdiff : ∀ N₁ N₂ : ℕ, N₁ ≠ 0 → N₂ ≠ 0 →
      PowerSeries.heckeV N₁ PEz - PowerSeries.heckeV N₂ PEz =
        PowerSeries.C x * (PowerSeries.heckeV N₁ Pσ - PowerSeries.heckeV N₂ Pσ) := by
    intro N₁ N₂ h₁ h₂
    rw [hPEz, heckeV_PE N₁ h₁, heckeV_PE N₂ h₂, ← hxdef, ← hPσ]; ring
  have hV1 : PowerSeries.heckeV 1 Pσ = Pσ := by ext n; simp [PowerSeries.coeff_heckeV]
  have hV1E : PowerSeries.heckeV 1 PEz = PEz := by ext n; simp [PowerSeries.coeff_heckeV]

  set Pε₁ : PowerSeries ℤ := PEz - PowerSeries.C ((p : ℤ) ^ a) * PowerSeries.heckeV p PEz with hPε₁
  set PεW₁ : PowerSeries ℤ := PowerSeries.C x' * (PowerSeries.heckeV p Pσ - Pσ) with hPεW₁
  have hpa : (p : ℂ) * (p : ℂ) ^ (a - 1) = (p : ℂ) ^ a := by
    rw [← pow_succ']; congr 1; omega
  have hcz : ((p : ℂ) ^ ((a : ℤ) - 2))⁻¹ * (p : ℂ) ^ (a - 1) = p := by
    have h3 : 3 ≤ a := three_le_wt (p := p)
    have : (p : ℂ) ^ (a - 1) = (p : ℂ) ^ ((a : ℤ) - 2) * p := by
      rw [← zpow_natCast, ← zpow_add_one₀ hpC]; congr 1; omega
    rw [this, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hpC), one_mul]
  have hε₁ : Pε₁.map ιℂ = ιℂ (s : ℤ) • qExpansion 1 (⇑ε : ℍ → ℂ) := by
    rw [hPε₁, map_sub, map_mul, PowerSeries.map_C, map_pow, map_natCast, hεdef, eps, ModularForm.coe_sub,
      ModularForm.qExpansion_sub one_pos h1Γ, ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1Γ,
      smul_sub, eq_intCast, Int.cast_natCast, hqE, smul_comm (s : ℂ) (p : ℂ), hqEW, smul_smul, hpa,
      PowerSeries.smul_eq_C_mul]
  have hε₁I : Pε₁.map (Ideal.Quotient.mk (Ideal.span {(p : ℤ)})) =
      PowerSeries.C (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}) (s : ℤ)) := by
    have hxI : Ideal.Quotient.mk (Ideal.span {(p : ℤ)}) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨x', hx'⟩)
    have hpaI : Ideal.Quotient.mk (Ideal.span {(p : ℤ)}) ((p : ℤ) ^ a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_pow_self _ (by omega)))
    rw [hPε₁, map_sub, map_mul, PowerSeries.map_C, hpaI, map_zero, zero_mul, sub_zero, hPEz, PE, map_add, map_mul,
      PowerSeries.map_C, PowerSeries.map_C, ← hxdef, hxI, map_zero, zero_mul, add_zero, ← hsdef]
  have hεW₁ : ((p : ℂ) ^ 2) • PεW₁.map ιℂ = ιℂ (s : ℤ) • qExpansion 1 (⇑εW : ℍ → ℂ) := by
    rw [hεWdef, epsW, ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1Γ, ModularForm.IsGLPos.coe_smul,
      ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1Γ, ModularForm.qExpansion_smul one_pos h1Γ,
      smul_sub, eq_intCast, Int.cast_natCast, smul_comm (s : ℂ), smul_comm (s : ℂ), hqE, hqEW, smul_smul, hcz,
      ← smul_sub, ← map_sub,
      show PowerSeries.heckeV p PEz - PEz = PowerSeries.heckeV p PEz - PowerSeries.heckeV 1 PEz by rw [hV1E],
      hVdiff p 1 hp0 one_ne_zero, hV1, hPεW₁, hx']
    rw [map_mul (PowerSeries.map ιℂ), map_mul (PowerSeries.map ιℂ), PowerSeries.map_C, PowerSeries.map_C,
      PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
    simp only [← mul_assoc]
    rw [← map_mul PowerSeries.C, ← map_mul PowerSeries.C]
    congr 2
    simp only [eq_intCast, Int.cast_natCast, map_mul]
    ring
  obtain ⟨PfW, hPfW⟩ := exists_intSeries_of_forall_mem_bot _ (hint d₀).2
  have hg₁ : pf.map ιℂ = ιℂ 1 • qExpansion 1 (⇑fM : ℍ → ℂ) := by
    rw [map_one, one_smul, hfM, coe_ofCusp]; exact hpf
  have hgW₁ : PfW.map ιℂ = (ιℂ 1 * (p : ℂ) ^ 0) • qExpansion 1 (⇑fW : ℍ → ℂ) := by
    rw [map_one, pow_zero, one_mul, one_smul, hfWdef, coe_ofCusp, hX₀]; exact hPfW
  obtain ⟨P₁, hP₁, hP₁I⟩ :=
    ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv hp W H hHpW ιℂ
      (Ideal.span {(p : ℤ)}) (Ideal.mem_span_singleton_self _) fM fW ε εW hfW hεW 1 1 (s : ℤ) (s : ℤ) 0 2
      pf PfW Pε₁ PεW₁ hg₁ hgW₁ hε₁ hε₁I hεW₁ i (by omega)

  set φ : ↥(integralClosure ℤ ℂ) →+* ℂ := algebraMap ↥(integralClosure ℤ ℂ) ℂ with hφ
  set ιO : ℤ →+* ↥(integralClosure ℤ ℂ) := Int.castRingHom ↥(integralClosure ℤ ℂ) with hιO
  have hφnat : ∀ n : ℕ, φ (n : ↥(integralClosure ℤ ℂ)) = (n : ℂ) := fun n => map_natCast φ n
  have hgAcoe : ⇑gA = ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f) := by rw [hgAdef, coe_ofCusp, hXe]
  set Pg₂ : PowerSeries ↥(integralClosure ℤ ℂ) := PowerSeries.C (((M / p : ℕ) : ↥(integralClosure ℤ ℂ)) ^ i) * pfW with hPg₂
  have hg₂ : Pg₂.map φ = φ ((Dn : ℕ) : ↥(integralClosure ℤ ℂ)) • qExpansion 1 (⇑g'' : ℍ → ℂ) := by
    rw [hφnat, hg'', ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1Γ, smul_comm,
      ← ModularForm.qExpansion_smul one_pos h1Γ, hgAcoe, ← hpfW, hPg₂, map_mul, PowerSeries.map_C, map_pow, hφnat,
      PowerSeries.smul_eq_C_mul]
  set PY : PowerSeries ↥(integralClosure ℤ ℂ) := PowerSeries.mk fun n =>
    (⟨(M : ℂ) ^ b * PowerSeries.coeff n (qExpansion 1 (⇑Y : ℍ → ℂ)), (mem_integralClosure_iff ℤ ℂ).mpr (hbY n)⟩ :
      ↥(integralClosure ℤ ℂ)) with hPY
  have hPYmap : PY.map φ = ((M : ℂ) ^ b) • qExpansion 1 (⇑Y : ℍ → ℂ) := by
    ext n; rw [PowerSeries.coeff_map, hPY, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]; rfl
  set PgW₂ : PowerSeries ↥(integralClosure ℤ ℂ) := PowerSeries.C (((M / p : ℕ) : ↥(integralClosure ℤ ℂ)) ^ i) * PY with hPgW₂
  have hMpQ : (M : ℂ) = (p : ℂ) * ((M / p : ℕ) : ℂ) := by exact_mod_cast M_eq hpM
  have hgW₂ : PgW₂.map φ = (φ (((M / p : ℕ) : ↥(integralClosure ℤ ℂ)) ^ b) * (p : ℂ) ^ b) • qExpansion 1 (⇑gW'' : ℍ → ℂ) := by
    rw [map_pow, hφnat, ← mul_pow, mul_comm ((M / p : ℕ) : ℂ), ← hMpQ, hgW'', ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos h1Γ, smul_comm, hgAWdef, coe_ofCusp, ← hPYmap, hPgW₂, map_mul, PowerSeries.map_C,
      map_pow, hφnat, PowerSeries.smul_eq_C_mul]
  set Pε₂ : PowerSeries ↥(integralClosure ℤ ℂ) :=
    (PowerSeries.C (((M / p : ℕ) : ℤ) ^ (a - 1)) * PowerSeries.heckeV (M / p) PEz -
      PowerSeries.C ((p : ℤ) * (M : ℤ) ^ (a - 1)) * PowerSeries.heckeV M PEz).map ιO with hPε₂
  have hε₂ : Pε₂.map φ = φ ((s : ℕ) : ↥(integralClosure ℤ ℂ)) • qExpansion 1 (⇑ε'' : ℍ → ℂ) := by
    rw [hφnat, hε'', epsA, ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1Γ, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos h1Γ, smul_sub, smul_comm (s : ℂ) (p : ℂ), hqEA, hqEWA, hPε₂, map_map_int, ← hιℂ,
      map_sub, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C, smul_smul, PowerSeries.smul_eq_C_mul,
      PowerSeries.smul_eq_C_mul]
    simp only [map_pow, map_mul, eq_intCast, Int.cast_natCast]
  set t : ↥(integralClosure ℤ ℂ) := ((M / p : ℕ) : ↥(integralClosure ℤ ℂ)) ^ (a - 1) * (s : ℕ) with ht
  have hpmk : ((p : ℕ) : ↥(integralClosure ℤ ℂ) ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), Ideal.Quotient.eq_zero_iff_mem]; exact hp𝔪
  have hιOx : (Ideal.Quotient.mk 𝔪).comp ιO x = 0 := by
    rw [hx', map_mul, map_natCast, hpmk, zero_mul]
  have hιOp : (Ideal.Quotient.mk 𝔪).comp ιO ((p : ℤ) * (M : ℤ) ^ (a - 1)) = 0 := by
    rw [map_mul, map_natCast, hpmk, zero_mul]
  have hε₂I : Pε₂.map (Ideal.Quotient.mk 𝔪) = PowerSeries.C (Ideal.Quotient.mk 𝔪 t) := by
    rw [hPε₂, map_map_int_quot, map_sub, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C, hιOp, map_zero, zero_mul,
      sub_zero, hPEz, heckeV_PE _ hQ0, map_add, map_mul, PowerSeries.map_C, PowerSeries.map_C, ← hxdef, hιOx, map_zero,
      zero_mul, add_zero, ← map_mul, ht, ← hsdef]
    congr 1
    simp only [map_mul, map_pow, map_natCast]
  set PεW₂ : PowerSeries ↥(integralClosure ℤ ℂ) :=
    (PowerSeries.C (((M / p : ℕ) : ℤ) ^ (a - 1) * x') * (PowerSeries.heckeV M Pσ - PowerSeries.heckeV (M / p) Pσ)).map ιO
    with hPεW₂
  have hMpow : ((p : ℂ) ^ ((a : ℤ) - 2))⁻¹ * (M : ℂ) ^ (a - 1) = (p : ℂ) * ((M / p : ℕ) : ℂ) ^ (a - 1) := by
    rw [hMpQ, mul_pow, ← mul_assoc, hcz]
  have hεW₂ : ((p : ℂ) ^ 2) • PεW₂.map φ = φ ((s : ℕ) : ↥(integralClosure ℤ ℂ)) • qExpansion 1 (⇑εW'' : ℍ → ℂ) := by
    rw [hφnat, hεW''def, epsAW, ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1Γ, ModularForm.IsGLPos.coe_smul,
      ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos h1Γ, ModularForm.qExpansion_smul one_pos h1Γ,
      smul_sub, smul_comm (s : ℂ), smul_comm (s : ℂ), hqEA, hqEWA, smul_smul, smul_smul, hMpow, mul_comm (p : ℂ) (_ ^ (a - 1)),
      mul_smul, mul_smul, ← smul_sub, ← smul_sub, ← map_sub, hVdiff M (M / p) (NeZero.ne M) hQ0, hPεW₂, map_map_int, ← hιℂ,
      hx']
    rw [map_mul (PowerSeries.map ιℂ), map_mul (PowerSeries.map ιℂ), PowerSeries.map_C, PowerSeries.map_C,
      PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
    simp only [← mul_assoc]
    rw [← map_mul PowerSeries.C, ← map_mul PowerSeries.C, ← map_mul PowerSeries.C]
    congr 2
    simp only [eq_intCast, Int.cast_natCast, map_mul, map_pow]
    ring
  obtain ⟨P₂, hP₂, hP₂I⟩ :=
    ModularForm.exists_map_eq_qExpansion_smul_trace_mul_pow_and_map_eq_of_slash_alGL_inv hp W H hHpW φ 𝔪 hp𝔪 g'' gW''
      ε'' εW'' hgW''slash hεW'' ((Dn : ℕ) : ↥(integralClosure ℤ ℂ)) (((M / p : ℕ) : ↥(integralClosure ℤ ℂ)) ^ b)
      ((s : ℕ) : ↥(integralClosure ℤ ℂ)) t b 2 Pg₂ PgW₂ Pε₂ PεW₂ hg₂ hgW₂ hε₂ hε₂I hεW₂ i (by omega)

  have hw : (2 : ℤ) + (i : ℤ) * (a : ℤ) = (2 : ℤ) + ((i * a : ℕ) : ℤ) := by push_cast; ring
  set TrF : ModularForm (Γ (M / p) (ModularCurve.infSubgroup p M H hpM)) (2 + (i : ℤ) * (a : ℤ)) :=
    ModularForm.trace (Γ (M / p) (ModularCurve.infSubgroup p M H hpM)) F with hTrF
  have hTrV : (⇑(ModularForm.trace (Γ W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) F) : ℍ → ℂ) = ⇑TrF := rfl
  have hTrK : (⇑(ModularForm.trace (Γ (M / p) H') F) : ℍ → ℂ) = ⇑TrF := rfl
  have hTrK' : (⇑(ModularForm.trace (Γ (M / p) H') F') : ℍ → ℂ) =
      ⇑(ModularForm.trace (Γ W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) (g''.mul (ε''.pow i))) := by
    rw [hFF]; rfl
  set G : ModularForm (Γ (M / p) (ModularCurve.infSubgroup p M H hpM)) ((2 : ℤ) + ((i * a : ℕ) : ℤ)) :=
    ((s ^ i : ℕ) : ℂ) • TrF.mcast hw with hGdef
  have hGcoe : (⇑G : ℍ → ℂ) = ((s : ℂ) ^ i) • ⇑TrF := by
    rw [hGdef, ModularForm.IsGLPos.coe_smul, ModularForm.coe_mcast]; push_cast; rfl
  have hdetWQ : 0 < ((Matrix.GeneralLinearGroup.det WQ : ℝˣ) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hWQ, Matrix.det_fin_two_of]
    have : (0 : ℝ) < ((M / p : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hQ0
    linarith
  refine ⟨i * a, G, P₁, s ^ i, Dn * (M / p) ^ b, P₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_pos hi1 wt_pos
  · exact dvd_mul_of_dvd_right sub_one_dvd_wt i
  · exact dvd_mul_of_dvd_right four_dvd_wt i
  · exact fun h => hps (hp.dvd_of_dvd_pow h)
  · exact fun h => (hp.dvd_mul.mp h).elim hD (fun h' => not_p_dvd_Q hpM hpM2 (hp.dvd_of_dvd_pow h'))
  ·
    show P₁.map (Int.castRingHom ℂ) = qExpansion 1 (⇑G : ℍ → ℂ)
    have hsc : ιℂ (1 * 1 * (s : ℤ) ^ i) = (s : ℂ) ^ i := by
      rw [one_mul, one_mul, map_pow, hιℂ, eq_intCast, Int.cast_natCast]
    rw [← hιℂ, hP₁, hGcoe, ← hTrV, ← hFdef, hsc]
  ·
    intro n
    have h := congrArg (PowerSeries.coeff n) hP₁I
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_C_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at h
    push_cast
    simpa using h
  ·
    rw [slash_congr_weight hw.symm (⇑G) WQ, hGcoe, ModularForm.smul_slash, ← hTrK, htr, hTrK', UpperHalfPlane.σ,
      if_pos hdetWQ]
    simp only [ContinuousAlgEquiv.refl_apply]
    rw [smul_smul]
    have hsc2 : ((Dn * (M / p) ^ b : ℕ) : ℂ) * (s : ℂ) ^ i =
        φ (((Dn : ℕ) : ↥(integralClosure ℤ ℂ)) * (((M / p : ℕ) : ↥(integralClosure ℤ ℂ)) ^ b) *
          ((s : ℕ) : ↥(integralClosure ℤ ℂ)) ^ i) := by
      simp only [map_mul, map_pow, hφnat]; push_cast; ring
    rw [hsc2, hP₂]
  ·
    intro n
    have h := congrArg (PowerSeries.coeff n) hP₂I
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_C_mul, hPg₂, PowerSeries.coeff_C_mul,
      Ideal.Quotient.eq] at h
    have h2 := 𝔪.mul_mem_left ((Dn : ℕ) : ↥(integralClosure ℤ ℂ)) h
    rw [mul_sub] at h2
    have hia : (a - 1) * i + i = i * a := by
      rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left i ha1), mul_comm]
    have hprod : (((Dn * (M / p) ^ b * s ^ i * (M / p) ^ (i * a) : ℕ)) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n pfW =
        ((Dn : ℕ) : ↥(integralClosure ℤ ℂ)) * ((((M / p : ℕ) : ↥(integralClosure ℤ ℂ))) ^ b * t ^ i *
          ((((M / p : ℕ) : ↥(integralClosure ℤ ℂ))) ^ i * PowerSeries.coeff n pfW)) := by
      rw [ht, mul_pow, ← pow_mul, ← hia, pow_add]; push_cast; ring
    rw [hprod]; exact h2

end MainProof

end SerreFrickeCSF
p2m_reactivate "P2MW.S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet.SerreFrickeCSF"

end
p2m_reactivate "P2MW.S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet.SerreFrickeCSF"

open scoped MatrixGroups ModularForm in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (𝔪 : Ideal ↥(integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime)
    (hp𝔪 : ((p : ℕ) : ↥(integralClosure ℤ ℂ)) ∈ 𝔪)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p))
    (e : (ZMod M)ˣ) (he : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((M / p : ℕ) : ℝ), 0])
    (f : CuspForm (CohCarrier.GammaH M H) 2)
    (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ))
    (pf : PowerSeries ℤ) (hpf : ModularCurve.IsIntegralQExp ⇑f pf)
    (D : ℕ) (hD : ¬ p ∣ D)
    (pfW : PowerSeries ↥(integralClosure ℤ ℂ))
    (hpfW : pfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
      UpperHalfPlane.qExpansion 1 ((D : ℂ) • ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))) :
    ∃ (w : ℕ) (G : ModularForm (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) : Subgroup (GL (Fin 2) ℝ)) ((2 : ℤ) + w))
      (P : PowerSeries ℤ) (D₁ D₂ : ℕ) (PGW : PowerSeries ↥(integralClosure ℤ ℂ)),
      0 < w ∧ (p - 1 ∣ w) ∧ (4 ∣ w) ∧ ¬ p ∣ D₁ ∧ ¬ p ∣ D₂ ∧
      ModularCurve.IsIntegralQExp ⇑G P ∧
      (∀ n : ℕ, (p : ℤ) ∣ PowerSeries.coeff n P - (D₁ : ℤ) * PowerSeries.coeff n pf) ∧
      PGW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) =
        UpperHalfPlane.qExpansion 1 ((D₂ : ℂ) • ((⇑G : UpperHalfPlane → ℂ) ∣[(2 : ℤ) + w] WQ)) ∧
      (∀ n : ℕ, ((D : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n PGW -
          ((D₂ * D₁ * (M / p) ^ w : ℕ) : ↥(integralClosure ℤ ℂ)) * PowerSeries.coeff n pfW ∈ 𝔪) :=
  SerreFrickeCSF.main p M H hpM hpM2 hHp 𝔪 h𝔪 hp𝔪 Wd e he WQ hWQ f hf pf hpf D hD pfW hpfW

end S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet
end P2MW
export P2MW.S_CuspForm_exists_isIntegralQExp_congr_and_qExpansion_slash_fricke_congr_of_mem_twoCuspIntegralSet (solution)
