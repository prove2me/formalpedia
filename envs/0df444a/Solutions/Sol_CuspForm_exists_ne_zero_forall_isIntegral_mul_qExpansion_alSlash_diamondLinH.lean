-- Prove2me | solution 1 for CuspForm.exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d05c6f82-26bd-565e-b6fd-422afcc007ee

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_alSlash
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open scoped MatrixGroups ModularForm

namespace AlH1aBlr

open ModularForm

theorem exists_gamma0_fricke_mul_eq_mat_mul_mat {M p Q : ℕ} [NeZero M] (hM : M = p * Q)
    (Wp : AtkinLehnerDatum M p) (Wq : AtkinLehnerDatum M Q) :
    ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 M ∧
      !![(0 : ℤ), -1; (M : ℤ), 0] * (γ₀ : Matrix (Fin 2) (Fin 2) ℤ) = Wp.mat * Wq.mat := by
  have hRp : Wp.R = Q := Nat.eq_of_mul_eq_mul_left Wp.q_pos (Wp.hM.symm.trans hM)
  have hRq : Wq.R = p := Nat.eq_of_mul_eq_mul_left Wq.q_pos (Wq.hM.symm.trans (hM.trans (mul_comm p Q)))

  let g : Matrix (Fin 2) (Fin 2) ℤ :=
    !![(Q : ℤ) * Wq.a + p, Wq.b + 1; -(M : ℤ) * (Wq.a * Wp.a + Wp.b), -((p : ℤ) * Wp.a * Wq.b + (Q : ℤ) * Wp.b)]
  have hprod : !![(0 : ℤ), -1; (M : ℤ), 0] * g = Wp.mat * Wq.mat := by
    have hMz : (M : ℤ) = (p : ℤ) * (Q : ℤ) := by exact_mod_cast hM
    rw [AtkinLehnerDatum.mat, AtkinLehnerDatum.mat, hRp, hRq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g, Matrix.mul_apply, Fin.sum_univ_two, hMz] <;> ring
  have hdet : g.det = 1 := by
    have h1 : (!![(0 : ℤ), -1; (M : ℤ), 0] * g).det = (Wp.mat * Wq.mat).det := by rw [hprod]
    rw [Matrix.det_mul, Matrix.det_mul, Wp.det_mat, Wq.det_mat, Matrix.det_fin_two_of] at h1
    have hMz : (M : ℤ) = (p : ℤ) * (Q : ℤ) := by exact_mod_cast hM
    have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    rw [← hMz] at h1
    have : (M : ℤ) * g.det = (M : ℤ) * 1 := by linear_combination h1
    exact mul_left_cancel₀ hM0 this
  refine ⟨⟨g, hdet⟩, ?_, hprod⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  show (((-(M : ℤ) * (Wq.a * Wp.a + Wp.b) : ℤ)) : ZMod M) = 0
  push_cast
  simp

noncomputable def frickeGL (M : ℕ) [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp] theorem frickeGL_coe (M : ℕ) [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

noncomputable def scalarGL (c : ℝ) (hc : c ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; exact pow_ne_zero _ hc)

@[scoped simp] theorem scalarGL_coe (c : ℝ) (hc : c ≠ 0) :
    ((scalarGL c hc : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := rfl

theorem scalarGL_mul_sqUnit_mul_alGL_eq {M p Q : ℕ} [NeZero M] (hM : M = p * Q)
    (Wp : AtkinLehnerDatum M p) (Wq : AtkinLehnerDatum M Q) :
    ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 M ∧
      scalarGL (p : ℝ) (by exact_mod_cast Wp.q_pos.ne') * Matrix.SpecialLinearGroup.mapGL ℝ Wp.sqUnitSL * Wq.alGL =
        Wp.alGL * frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ₀ := by
  obtain ⟨γ₀, hγ₀, hprod⟩ := exists_gamma0_fricke_mul_eq_mat_mul_mat hM Wp Wq
  refine ⟨γ₀, hγ₀, ?_⟩

  apply Units.ext
  have hsq := Wp.mat_sq

  have hL : ((scalarGL (p : ℝ) (by exact_mod_cast Wp.q_pos.ne') * Matrix.SpecialLinearGroup.mapGL ℝ Wp.sqUnitSL * Wq.alGL :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Wp.mat * Wp.mat * Wq.mat).map (Int.castRingHom ℝ) := by
    rw [hsq, Units.val_mul, Units.val_mul, scalarGL_coe, AtkinLehnerDatum.alGL_coe, Matrix.map_mul, Matrix.smul_mul,
      Matrix.map_smul', Matrix.smul_mul, Matrix.one_mul]
    · congr 1
      ext i j
      simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, AtkinLehnerDatum.sqUnitSL]
    all_goals intros; simp
  have hR : ((Wp.alGL * frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (Wp.mat * (!![(0 : ℤ), -1; (M : ℤ), 0] * (γ₀ : Matrix (Fin 2) (Fin 2) ℤ))).map (Int.castRingHom ℝ) := by
    rw [Units.val_mul, Units.val_mul, AtkinLehnerDatum.alGL_coe, frickeGL_coe, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc]
    · congr 2
      all_goals
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    all_goals intros; simp
  rw [hL, hR, hprod, Matrix.mul_assoc]

open UpperHalfPlane in

theorem slash_scalarGL {c : ℝ} (hc : 0 < c) (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] scalarGL c hc.ne' = ((c : ℂ) ^ (k - 2)) • f := by
  have hdet : ((scalarGL c hc.ne').det : ℝ) = c ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hdetpos : 0 < ((scalarGL c hc.ne').det : ℝ) := by rw [hdet]; positivity
  have hsmul : ∀ τ : ℍ, (scalarGL c hc.ne') • τ = τ := by
    intro τ
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, scalarGL, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.smul_apply, hc.ne']
  ext τ
  rw [ModularForm.slash_apply, hsmul, Pi.smul_apply, smul_eq_mul]
  have hσ : UpperHalfPlane.σ (scalarGL c hc.ne') (f τ) = f τ := by
    rw [UpperHalfPlane.σ, if_pos hdetpos]; rfl
  rw [hσ, hdet, UpperHalfPlane.denom]
  have h10 : ((scalarGL c hc.ne' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp [scalarGL_coe]
  have h11 : ((scalarGL c hc.ne' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = c := by simp [scalarGL_coe]
  rw [h10, h11, abs_of_pos (pow_pos hc 2)]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  rw [zero_mul, zero_add, ← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hc0, mul_comm]
  congr 2
  push_cast; ring

theorem σ_apply_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < (g.det : ℝ)) (z : ℂ) : UpperHalfPlane.σ g z = z := by
  rw [UpperHalfPlane.σ, if_pos hg]; rfl

theorem det_mapGL_pos (γ : SL(2, ℤ)) : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ γ).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have : ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (γ.map (Int.castRingHom ℝ))
    convert h using 2 <;> rfl
  rw [this]; exact one_pos

open UpperHalfPlane in

theorem smul_slash_sqUnit_alSlash_eq {M p Q : ℕ} [NeZero M] (hM : M = p * Q)
    (Wp : AtkinLehnerDatum M p) (Wq : AtkinLehnerDatum M Q) :
    ∃ γ₀ : SL(2, ℤ), γ₀ ∈ CongruenceSubgroup.Gamma0 M ∧ ∀ (k : ℤ) (f : ℍ → ℂ),
      ((p : ℂ) ^ (k - 2)) • alSlash Wq k (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ Wp.sqUnitSL : GL (Fin 2) ℝ)) =
        ((alSlash Wp k f) ∣[k] frickeGL M) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) := by
  obtain ⟨γ₀, hγ₀, hGL⟩ := scalarGL_mul_sqUnit_mul_alGL_eq hM Wp Wq
  refine ⟨γ₀, hγ₀, fun k f => ?_⟩
  have hp : (0 : ℝ) < p := by exact_mod_cast Wp.q_pos
  have h := congrArg (fun g : GL (Fin 2) ℝ => f ∣[k] g) hGL
  beta_reduce at h
  rw [SlashAction.slash_mul, SlashAction.slash_mul, SlashAction.slash_mul, SlashAction.slash_mul,
    show scalarGL (p : ℝ) (by exact_mod_cast Wp.q_pos.ne') = scalarGL (p : ℝ) hp.ne' from rfl,
    slash_scalarGL hp k f, ModularForm.smul_slash, ModularForm.smul_slash, σ_apply_of_det_pos (det_mapGL_pos _),
    σ_apply_of_det_pos Wq.det_alGL_pos] at h
  rw [alSlash_def, alSlash_def, ← h]
  push_cast
  rfl

end AlH1aBlr
p2m_reactivate "P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH.AlH1aBlr"

namespace ModularCurve p2m_export "ModularCurve" "restrictForm coe_restrictForm IsIntegralQExp exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion exists_isIntegralQExp_smul_slash_of_mem_Gamma0" end ModularCurve
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.exists_ne_zero_forall_isIntegral_natCast_mul_sum_mul_coeff
    (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (ι : AlgebraicClosure ℚ →+* ℂ) (P : Fin n → PowerSeries ℤ) :
    ∃ D₀ : ℕ, D₀ ≠ 0 ∧ ∀ m : ℕ,
      IsIntegral ℤ ((D₀ : ℂ) * ∑ i, ι (c i) * ((PowerSeries.coeff m (P i) : ℤ) : ℂ)) := by
  classical
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)

  have hmult : ∀ i, ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : AlgebraicClosure ℚ) * c i) := by
    intro i
    have hQ : IsAlgebraic ℚ (c i) := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic (c i)
    have halg : IsAlgebraic ℤ (c i) := IsAlgebraic.restrictScalars (R := ℤ) (S := ℚ) hQ
    obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
    exact ⟨y, hy0, by rwa [← zsmul_eq_mul]⟩
  choose d hd0 hdint using hmult
  refine ⟨∏ i, (d i).natAbs, ?_, fun m => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun i _ => Int.natAbs_ne_zero.mpr (hd0 i)
  · rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_

    obtain ⟨k, hk⟩ : ∃ k : ℤ, ((∏ j, (d j).natAbs : ℕ) : ℤ) = k * d i := by
      refine ⟨(∏ j ∈ Finset.univ.erase i, ((d j).natAbs : ℤ)) * (d i).sign, ?_⟩
      rw [Nat.cast_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ((d j).natAbs : ℤ)) (Finset.mem_univ i),
        mul_assoc, Int.sign_mul_self_eq_natAbs, mul_comm]
    have : ((∏ j, (d j).natAbs : ℕ) : ℂ) * (ι (c i) * ((PowerSeries.coeff m (P i) : ℤ) : ℂ))
        = ((k * PowerSeries.coeff m (P i) : ℤ) : ℂ) * ι ((d i : AlgebraicClosure ℚ) * c i) := by
      rw [map_mul, map_intCast, show ((∏ j, (d j).natAbs : ℕ) : ℂ) = (((∏ j, (d j).natAbs : ℕ) : ℤ) : ℂ) by norm_cast, hk]
      push_cast
      ring
    rw [this]
    exact (isIntegral_algebraMap (R := ℤ) (x := k * PowerSeries.coeff m (P i))).mul (map_isIntegral_int ι (hdint i))

namespace AlModBlr

theorem gamma1_le_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨h00, h11, h10⟩ := hA
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by rw [CongruenceSubgroup.Gamma0_mem]; exact h10
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext; rw [CohCarrier.val_gamma0Units, Units.val_one]; exact h11
  rw [this]; exact one_mem H

def restrictCusp {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (F : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm (CongruenceSubgroup.Gamma1 M) k where
  toFun := ⇑F
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq F A (Subgroup.map_mono (gamma1_le_gammaH M H) hA)
  holo' := CuspFormClass.holo F
  zero_at_cusps' hc := CuspFormClass.zero_at_cusps F (hc.mono (Subgroup.map_mono (gamma1_le_gammaH M H)))

@[scoped simp] theorem coe_restrictCusp {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {k : ℤ} (F : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(restrictCusp F) : UpperHalfPlane → ℂ) = ⇑F := rfl

end AlModBlr
p2m_reactivate "P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH.AlH1aBlr P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH.AlModBlr"

namespace AlH1aBlr
open ModularForm

theorem gammaH_bot_le_gamma1 (M : ℕ) [NeZero M] :
    CohCarrier.GammaH M (⊥ : Subgroup (ZMod M)ˣ) ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff] at hA
  obtain ⟨hA0, h1⟩ := hA
  rw [Subgroup.mem_bot] at h1
  have hd : ((A 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h1
    simpa [CohCarrier.val_gamma0Units, CongruenceSubgroup.Gamma0Map] using this
  have hc : ((A 1 0 : ℤ) : ZMod M) = 0 := (CongruenceSubgroup.Gamma0_mem).mp hA0
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, hd, hc⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe A
  rw [Matrix.det_fin_two] at hdet
  have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at this
  rw [hd, hc, mul_one, mul_zero, sub_zero] at this
  exact this

end AlH1aBlr
p2m_reactivate "P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH.AlH1aBlr P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH.AlModBlr"

open AlH1aBlr AlModBlr ModularForm in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (Wd : ModularForm.AtkinLehnerDatum M (M / p)) (e : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) 2) (hf : f ∈ CuspForm.twoCuspIntegralSet M H 2 p (⊥ : Subring ℂ)) :
    ∃ D₀ : ℕ, D₀ ≠ 0 ∧ ∀ n : ℕ, IsIntegral ℤ ((D₀ : ℂ) * (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash Wd 2 ⇑(CuspForm.diamondLinH 2 e f))).coeff n) := by
  classical
  have hp : p.Prime := Fact.out
  have hM : M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
  have hD : CuspForm.StableD M H 2 := CuspForm.stableD M H 2

  have hcop : Nat.Coprime p (M / p) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpM2 ?_
    rw [pow_two]; exact Nat.mul_dvd_of_dvd_div hpM h
  let Wp : ModularForm.AtkinLehnerDatum M p :=
    { R := M / p, hM := hM, a := Nat.gcdA p (M / p), b := -Nat.gcdB p (M / p), bezout := by
        have h := Nat.gcd_eq_gcd_ab p (M / p)
        rw [Nat.Coprime.gcd_eq_one hcop, Nat.cast_one] at h
        linear_combination -h }

  obtain ⟨γ₀, hγ₀, hformula⟩ := smul_slash_sqUnit_alSlash_eq hM Wp Wd

  set u : CongruenceSubgroup.Gamma0 M := ⟨Wp.sqUnitSL, Wp.sqUnitSL_mem⟩ with hu
  let d' : (ZMod M)ˣ := CohCarrier.gamma0Units M u⁻¹
  set fe := CuspForm.diamondLinH 2 e f with hfe
  set f' := CuspForm.diamondLinH 2 d' fe with hf'
  have hf'u : (⇑f' : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ Wp.sqUnitSL : GL (Fin 2) ℝ) = ⇑fe := by
    rw [hf', CuspForm.coe_diamondLinH_eq_slash 2 hD d' (u⁻¹) rfl fe, ← SlashAction.slash_mul, ← map_mul]
    have : ((u⁻¹ : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) * Wp.sqUnitSL = 1 := by
      rw [show Wp.sqUnitSL = ((u : CongruenceSubgroup.Gamma0 M) : SL(2, ℤ)) from rfl, Subgroup.coe_inv, inv_mul_cancel]
    rw [this, map_one, SlashAction.slash_one]
  have hX : ModularForm.alSlash Wd 2 ⇑fe =
      ((ModularForm.alSlash Wp 2 ⇑f') ∣[(2 : ℤ)] frickeGL M) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) := by
    have h := hformula 2 ⇑f'
    rw [hf'u, show ((2 : ℤ) - 2) = 0 by norm_num, zpow_zero, one_smul] at h
    exact h

  obtain ⟨G, hG⟩ := CuspForm.exists_gamma1_coe_eq_alSlash M p Wp (restrictCusp f')
  rw [coe_restrictCusp] at hG
  have hGint : ∀ n : ℕ, ∃ z : ℤ, (z : ℂ) = (UpperHalfPlane.qExpansion 1 ⇑G).coeff n := by
    intro n
    have ht : (CuspForm.diamondLinH 2 d' * CuspForm.diamondLinH 2 e : CuspForm (CohCarrier.GammaH M H) 2 →ₗ[ℂ] _) ∈
        CuspForm.heckeRingH M H 2 :=
      Subring.mul_mem _ (CuspForm.heckeGenH_mem_heckeRingH ∅ 2 (.dia d')) (CuspForm.heckeGenH_mem_heckeRingH ∅ 2 (.dia e))
    have h := (hf _ ht Wp n).2
    rw [Subring.mem_bot] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [hz, hG]
    rfl

  let G' : ModularForm (CohCarrier.GammaH M (⊥ : Subgroup (ZMod M)ˣ)) 2 :=
    ModularCurve.restrictForm (Subgroup.map_mono (gammaH_bot_le_gamma1 M)) (ModularFormClass.modularForm G)
  have hG' : (⇑G' : UpperHalfPlane → ℂ) = ⇑G := rfl
  have hG'rat : ∀ n : ℕ, ∃ r : ℚ, (UpperHalfPlane.qExpansion 1 ⇑G').coeff n = (r : ℂ) := by
    intro n
    obtain ⟨z, hz⟩ := hGint n
    exact ⟨z, by rw [hG', ← hz]; push_cast; rfl⟩

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let ιb : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom

  obtain ⟨N, c, g, P, hgP, hFr⟩ := ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion M ⊥ G' hG'rat ιb
    (frickeGL M) (frickeGL_coe M)

  have hgi : ∀ i : Fin N, ∃ (D : ℤ) (f₁ : ModularForm (CongruenceSubgroup.Gamma1 M) 2) (p₁ : PowerSeries ℤ),
      D ≠ 0 ∧ ModularCurve.IsIntegralQExp f₁ p₁ ∧
        (⇑f₁ : UpperHalfPlane → ℂ) = (D : ℂ) • ((⇑(g i) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ₀) := by
    intro i
    have := ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0 M
      (ModularCurve.restrictForm (Subgroup.map_mono (gamma1_le_gammaH M ⊥)) (g i))
      (p := P i) (by rw [ModularCurve.IsIntegralQExp, ModularCurve.coe_restrictForm]; exact hgP i) γ₀ hγ₀
    simpa only [ModularCurve.coe_restrictForm] using this
  choose Di f₁ p₁ hDi hf₁ hf₁eq using hgi

  have hXsum : ModularForm.alSlash Wd 2 ⇑fe = ∑ i, (ιb (c i) / (Di i : ℂ)) • (⇑(f₁ i) : UpperHalfPlane → ℂ) := by
    rw [hX, ← hG, ← hG', hFr]
    have hlin : ∀ (s : Finset (Fin N)), (∑ i ∈ s, ιb (c i) • (⇑(g i) : UpperHalfPlane → ℂ)) ∣[(2 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ₀ : GL (Fin 2) ℝ) = ∑ i ∈ s, ιb (c i) • ((⇑(g i) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ₀) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [SlashAction.zero_slash]
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, SlashAction.add_slash, ih, ModularForm.smul_slash,
          σ_apply_of_det_pos (det_mapGL_pos γ₀)]
        rfl
    rw [hlin]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf₁eq i, smul_smul, div_mul_cancel₀ _ (by exact_mod_cast hDi i)]

  have hcoeff : ∀ m : ℕ, (UpperHalfPlane.qExpansion 1 (ModularForm.alSlash Wd 2 ⇑fe)).coeff m =
      ∑ i, ιb (c i / (Di i : AlgebraicClosure ℚ)) * ((PowerSeries.coeff m (p₁ i) : ℤ) : ℂ) := by
    intro m
    have hΓ1 : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples _

    let Y : ModularForm (CongruenceSubgroup.Gamma1 M) 2 := ∑ i, (ιb (c i) / (Di i : ℂ)) • f₁ i
    have hcoesum : ∀ s : Finset (Fin N), (⇑(∑ i ∈ s, (ιb (c i) / (Di i : ℂ)) • f₁ i : ModularForm (CongruenceSubgroup.Gamma1 M) 2) :
        UpperHalfPlane → ℂ) = ∑ i ∈ s, (ιb (c i) / (Di i : ℂ)) • (⇑(f₁ i) : UpperHalfPlane → ℂ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ModularForm.coe_add, ModularForm.IsGLPos.coe_smul, ih]
    have hY : (⇑Y : UpperHalfPlane → ℂ) = ∑ i, (ιb (c i) / (Di i : ℂ)) • (⇑(f₁ i) : UpperHalfPlane → ℂ) := hcoesum _
    rw [hXsum, ← hY, show UpperHalfPlane.qExpansion 1 ⇑Y = ModularForm.qExpansionAddHom one_pos hΓ1 2 Y from rfl,
      map_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ModularForm.qExpansionAddHom one_pos hΓ1 2 ((ιb (c i) / (Di i : ℂ)) • f₁ i) =
        UpperHalfPlane.qExpansion 1 ⇑((ιb (c i) / (Di i : ℂ)) • f₁ i) from rfl,
      ModularForm.IsGLPos.coe_smul, UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero (f₁ i) one_pos hΓ1),
      ← (hf₁ i), map_smul, PowerSeries.coeff_map, smul_eq_mul, map_div₀, eq_intCast]
    congr 1
    rw [map_intCast]

  obtain ⟨D₀, hD₀, hint⟩ := ModularCurve.exists_ne_zero_forall_isIntegral_natCast_mul_sum_mul_coeff N
    (fun i => c i / (Di i : AlgebraicClosure ℚ)) ιb p₁
  exact ⟨D₀, hD₀, fun n => by rw [hcoeff n]; exact hint n⟩

end S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH
end P2MW
export P2MW.S_CuspForm_exists_ne_zero_forall_isIntegral_mul_qExpansion_alSlash_diamondLinH (solution)
