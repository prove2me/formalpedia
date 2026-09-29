-- Prove2me | solution 1 for CuspForm.exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3e88cc70-8e85-57f3-a93f-52045ecaa715

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup CohCarrier

namespace AlDiaFactor

variable {M : ℕ} {Q : ℕ}

theorem Q_dvd (W : ModularForm.AtkinLehnerDatum M Q) : Q ∣ M := Dvd.intro W.R W.hM.symm

theorem R_dvd (W : ModularForm.AtkinLehnerDatum M Q) : W.R ∣ M := Dvd.intro_left Q W.hM.symm

variable [NeZero M] (W : ModularForm.AtkinLehnerDatum M Q)

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem exists_alGL_mul_eq_factor {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ γ = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
        = 1 ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) := by
  obtain ⟨δ, hδ, hW⟩ := ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq W hγ
  refine ⟨δ, hδ, hW, ?_, ?_⟩
  ·
    have h01 := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hW
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_coe,
      mapGL_coe_eq, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] at h01
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, eq_intCast] at h01
    have hZ : (Q : ℤ) * W.a * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + W.b * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * W.b + (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (Q : ℤ) := by
      exact_mod_cast h01

    have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        - (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe δ
      rw [Matrix.det_fin_two] at this
      linear_combination this
    have hMδ : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      have := Gamma0_mem.mp hδ
      rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hQδ : (Q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
      (Int.natCast_dvd_natCast.mpr (Q_dvd W)).trans hMδ
    obtain ⟨s, hs⟩ := hQδ

    have hb : ((W.b : ℤ) : ZMod Q) * (-((W.R : ℕ) : ZMod Q)) = 1 := by
      have h := congrArg (fun z : ℤ => (z : ZMod Q)) W.bezout
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_sub,
        Int.cast_one] at h
      linear_combination h
    have h1 : ((W.b : ℤ) : ZMod Q) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
        = ((W.b : ℤ) : ZMod Q) * ((((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ)) : ZMod Q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod Q)) hZ
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, zero_add,
        mul_zero, add_zero] at h
      linear_combination h
    have h2 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod Q) := by
      have := congrArg (fun z : ZMod Q => (-((W.R : ℕ) : ZMod Q)) * z) h1
      simp only [← mul_assoc] at this
      rwa [mul_comm (-((W.R : ℕ) : ZMod Q)), hb, one_mul, one_mul] at this
    have h3 : (((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod Q) * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) = 1 := by
      have h := congrArg (fun z : ℤ => (z : ZMod Q)) hdet
      rw [hs] at h
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, mul_zero,
        sub_zero, Int.cast_one] at h
      exact h
    rw [h2, mul_comm]
    exact h3
  ·
    have h11 := congrArg (fun A : GL (Fin 2) ℝ => (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hW
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ModularForm.AtkinLehnerDatum.alGL_coe,
      mapGL_coe_eq, Matrix.map_apply, ModularForm.AtkinLehnerDatum.mat] at h11
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, eq_intCast] at h11
    have hZ : (Q : ℤ) * (W.R : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (Q : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * W.b + (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (Q : ℤ) := by
      exact_mod_cast h11

    have hMδ : (M : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      have := Gamma0_mem.mp hδ
      rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hRδ : ((W.R : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
      (Int.natCast_dvd_natCast.mpr (R_dvd W)).trans hMδ
    obtain ⟨s, hs⟩ := hRδ

    have ha : ((Q : ℕ) : ZMod W.R) * ((W.a : ℤ) : ZMod W.R) = 1 := by
      have h := congrArg (fun z : ℤ => (z : ZMod W.R)) W.bezout
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero,
        Int.cast_one] at h
      exact h
    have h1 : ((Q : ℕ) : ZMod W.R) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R)
        = ((Q : ℕ) : ZMod W.R) * (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) := by
      have h := congrArg (fun z : ℤ => (z : ZMod W.R)) hZ
      rw [hs] at h
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, mul_zero,
        zero_add] at h
      linear_combination h
    have h2 := congrArg (fun z : ZMod W.R => ((W.a : ℤ) : ZMod W.R) * z) h1
    have e : ∀ z : ZMod W.R, ((W.a : ℤ) : ZMod W.R) * (((Q : ℕ) : ZMod W.R) * z) = z := fun z => by
      rw [← mul_assoc, mul_comm ((W.a : ℤ) : ZMod W.R), ha, one_mul]
    simp only [e] at h2
    exact h2.symm

theorem coe_alGL_mul_alGL :
    ((W.alGL * W.alGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Q : ℝ) • ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hmul : ((W.alGL * W.alGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (W.mat * W.mat).map (algebraMap ℤ ℝ) := by
    rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, Matrix.map_mul]
  rw [hmul, W.mat_sq, mapGL_coe_eq, ModularForm.AtkinLehnerDatum.sqUnitSL_coe]
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, smul_eq_mul,
    eq_intCast, eq_intCast]
  push_cast
  ring

theorem mapGL_mul_alGL_mul_alGL (σ : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ σ * (W.alGL * W.alGL) =
      (W.alGL * W.alGL) * Matrix.SpecialLinearGroup.mapGL ℝ (W.sqUnitSL⁻¹ * σ * W.sqUnitSL) := by
  apply Units.ext
  have hL : ((Matrix.SpecialLinearGroup.mapGL ℝ σ * (W.alGL * W.alGL) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Q : ℝ) • ((Matrix.SpecialLinearGroup.mapGL ℝ (σ * W.sqUnitSL) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Units.val_mul, coe_alGL_mul_alGL, Matrix.mul_smul, map_mul, Units.val_mul]
  have hR : (((W.alGL * W.alGL) * Matrix.SpecialLinearGroup.mapGL ℝ (W.sqUnitSL⁻¹ * σ * W.sqUnitSL) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (Q : ℝ) • ((Matrix.SpecialLinearGroup.mapGL ℝ (σ * W.sqUnitSL) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Units.val_mul, coe_alGL_mul_alGL, Matrix.smul_mul, ← Units.val_mul, ← map_mul, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul]
  rw [hL, hR]

theorem exists_mapGL_mul_alGL_eq {σ : SL(2, ℤ)} (hσ : σ ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      Matrix.SpecialLinearGroup.mapGL ℝ σ * W.alGL = W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ δ ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q) * (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod Q)
        = 1 ∧
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) = (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod W.R) := by

  set γ : SL(2, ℤ) := W.sqUnitSL⁻¹ * σ * W.sqUnitSL with hγdef
  have hu : W.sqUnitSL ∈ Gamma0 M := W.sqUnitSL_mem
  have hγ : γ ∈ Gamma0 M := (Gamma0 M).mul_mem ((Gamma0 M).mul_mem ((Gamma0 M).inv_mem hu) hσ) hu
  obtain ⟨δ, hδ, hW, hQ, hR⟩ := exists_alGL_mul_eq_factor W hγ

  have hγσ : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = (((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) := by
    have h := map_mul (gamma0Units M) (⟨W.sqUnitSL⁻¹ * σ, (Gamma0 M).mul_mem ((Gamma0 M).inv_mem hu) hσ⟩ : Gamma0 M)
      ⟨W.sqUnitSL, hu⟩
    have h' := map_mul (gamma0Units M) (⟨W.sqUnitSL⁻¹, (Gamma0 M).inv_mem hu⟩ : Gamma0 M) ⟨σ, hσ⟩
    have hinv := map_inv (gamma0Units M) (⟨W.sqUnitSL, hu⟩ : Gamma0 M)
    have e1 : (⟨W.sqUnitSL⁻¹ * σ, (Gamma0 M).mul_mem ((Gamma0 M).inv_mem hu) hσ⟩ : Gamma0 M) =
        ⟨W.sqUnitSL⁻¹, (Gamma0 M).inv_mem hu⟩ * ⟨σ, hσ⟩ := rfl
    have e2 : (⟨γ, hγ⟩ : Gamma0 M) =
        (⟨W.sqUnitSL⁻¹ * σ, (Gamma0 M).mul_mem ((Gamma0 M).inv_mem hu) hσ⟩ : Gamma0 M) * ⟨W.sqUnitSL, hu⟩ := rfl
    have e3 : (⟨W.sqUnitSL⁻¹, (Gamma0 M).inv_mem hu⟩ : Gamma0 M) = (⟨W.sqUnitSL, hu⟩ : Gamma0 M)⁻¹ := rfl
    have hg : gamma0Units M ⟨γ, hγ⟩ = gamma0Units M ⟨σ, hσ⟩ := by
      rw [e2, h, e1, h', e3, hinv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hg
    simp [val_gamma0Units] at this
    exact this
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  ·
    have key : Matrix.SpecialLinearGroup.mapGL ℝ σ * W.alGL * W.alGL =
        W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by
      rw [mul_assoc, mapGL_mul_alGL_mul_alGL W σ, ← hγdef, mul_assoc, hW, ← mul_assoc]
    exact mul_right_cancel key
  · have hc : ((( ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod Q) =
        ((( ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod Q) := by rw [hγσ]
    rw [ZMod.cast_intCast (Q_dvd W), ZMod.cast_intCast (Q_dvd W)] at hc
    rw [← hc]
    exact hQ
  · have hc : ((( ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod W.R) =
        ((( ((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod W.R) := by rw [hγσ]
    rw [ZMod.cast_intCast (R_dvd W), ZMod.cast_intCast (R_dvd W)] at hc
    rw [← hc]
    exact hR

omit [NeZero M] in

theorem unitsMap_gamma0Units_val {D : ℕ} (hD : D ∣ M) (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M) :
    ((ZMod.unitsMap hD (gamma0Units M ⟨δ, hδ⟩) : (ZMod D)ˣ) : ZMod D) =
      (((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod D) := by
  rw [ZMod.unitsMap_val, val_gamma0Units]
  show ((((((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)).cast : ZMod D)) = _
  rw [ZMod.cast_intCast hD]

end AlDiaFactor

end

open scoped MatrixGroups ModularForm in
open AlDiaFactor CongruenceSubgroup CohCarrier in

theorem solution
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (d : (ZMod M)ˣ) (f G : CuspForm (CohCarrier.GammaH M H) k)
    (hG : (⇑G : UpperHalfPlane → ℂ) = ModularForm.alSlash W k ⇑f) :
    ∃ d' : (ZMod M)ˣ,
      ZMod.unitsMap (Dvd.intro_left q W.hM.symm : W.R ∣ M) d' = ZMod.unitsMap (Dvd.intro_left q W.hM.symm : W.R ∣ M) d ∧
      ZMod.unitsMap (Dvd.intro W.R W.hM.symm : q ∣ M) (d' * d) = 1 ∧
      ModularForm.alSlash W k (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) =
        (⇑(CuspForm.diamondLinH k d' G) : UpperHalfPlane → ℂ) := by

  set σ : Gamma0 M := CuspForm.gammaLift M d with hσdef
  obtain ⟨δ, hδ, hWδ, hQ, hR⟩ := exists_mapGL_mul_alGL_eq W σ.2
  have hσd : gamma0Units M σ = d := CuspForm.gamma0Units_gammaLift d
  have hσval : (((( σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = (d : ZMod M) := by
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hσd
    simp only [val_gamma0Units] at this
    exact this
  refine ⟨gamma0Units M ⟨δ, hδ⟩, ?_, ?_, ?_⟩
  ·
    ext
    rw [unitsMap_gamma0Units_val, hR, ZMod.unitsMap_val]
    have : ((d : ZMod M).cast : ZMod W.R) = ((((( σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M).cast : ZMod W.R) := by
      rw [hσval]
    rw [this, ZMod.cast_intCast (R_dvd W)]
  ·
    ext
    rw [ZMod.unitsMap_val, Units.val_mul, val_gamma0Units, Units.val_one, ← hσval]
    show ((((((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) * (((( σ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M)).cast : ZMod q)) = 1
    rw [ZMod.cast_mul (Q_dvd W), ZMod.cast_intCast (Q_dvd W), ZMod.cast_intCast (Q_dvd W)]
    exact hQ
  ·
    by_cases hD : CuspForm.StableD M H k
    · rw [CuspForm.coe_diamondLinH_apply k hD d f,
        CuspForm.coe_diamondLinH_eq_slash k hD (gamma0Units M ⟨δ, hδ⟩) ⟨δ, hδ⟩ rfl G, hG,
        ModularForm.alSlash_def, ModularForm.alSlash_def, ← SlashAction.slash_mul, ← SlashAction.slash_mul,
        ← hσdef]
      exact congrArg (fun A : GL (Fin 2) ℝ => (⇑f : UpperHalfPlane → ℂ) ∣[k] A) hWδ
    · have h0 : ∀ e : (ZMod M)ˣ, (CuspForm.diamondLinH k e : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = 0 :=
        fun e => by rw [CuspForm.diamondLinH, dif_neg hD]
      rw [h0 d, h0, LinearMap.zero_apply, LinearMap.zero_apply, ModularForm.alSlash_def]
      show (⇑(0 : CuspForm (CohCarrier.GammaH M H) k) : UpperHalfPlane → ℂ) ∣[k] W.alGL = ⇑(0 : CuspForm (CohCarrier.GammaH M H) k)
      rw [CuspForm.coe_zero, SlashAction.zero_slash]

end S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum
end P2MW
export P2MW.S_CuspForm_exists_alSlash_diamondLinH_eq_diamondLinH_alSlash_atkinLehnerDatum (solution)
