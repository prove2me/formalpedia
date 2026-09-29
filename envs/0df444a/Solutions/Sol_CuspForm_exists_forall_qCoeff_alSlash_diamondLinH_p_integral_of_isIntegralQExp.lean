-- Prove2me | solution 1 for CuspForm.exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/712cc9ac-b358-5ec9-bc5b-c57188ad61ac

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularFormClass ModularCurve CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace RES
namespace WBDD

variable {M p : ℕ} [NeZero M]

theorem Gamma1_le_GammaH {N : ℕ} (H : Subgroup (ZMod N)ˣ) : Gamma1 N ≤ CohCarrier.GammaH N H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨-, h11, h10⟩ := hA
  have hA0 : A ∈ Gamma0 N := Gamma0_mem.mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units N ⟨A, hA0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h11
  rw [this]; exact one_mem H

scoped instance finiteIndex_GammaH (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH H)

omit [NeZero M] in
theorem T_mem_GammaH (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH H (by rw [Gamma1_mem]; simp [ModularGroup.T])

variable (W : ModularForm.AtkinLehnerDatum M p)

omit [NeZero M] in

theorem inf_le_GammaH (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H) :
    (Gamma1 W.R ⊓ Gamma0 (W.R * p) : Subgroup SL(2, ℤ)) ≤ CohCarrier.GammaH M H := by
  intro A hA
  obtain ⟨hA1, hA0⟩ := Subgroup.mem_inf.mp hA
  have hM : W.R * p = M := by rw [mul_comm]; exact W.hM.symm
  have hA0' : A ∈ Gamma0 M := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hA0 ⊢
    rwa [hM] at hA0
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0', hHp _ ?_⟩
  apply Units.ext
  rw [ZMod.unitsMap, Units.coe_map, Units.val_one]
  show ZMod.castHom (Dvd.intro_left p W.hM.symm) (ZMod W.R) ((CohCarrier.gamma0Units M ⟨A, hA0'⟩ : ZMod M)) = 1
  rw [CohCarrier.val_gamma0Units]
  show ZMod.castHom (Dvd.intro_left p W.hM.symm) (ZMod W.R) (((A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = 1
  rw [map_intCast]
  rw [Gamma1_mem] at hA1
  exact hA1.2.1

def restrict (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    [NeZero W.R] {k : ℤ} (F : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm ((Gamma1 W.R ⊓ Gamma0 (W.R * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑F
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ (inf_le_GammaH W H hHp hg))
  holo' := CuspFormClass.holo F
  bdd_at_cusps' := fun {c} hc γ hγ => by
    have hc' : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) :=
      hc.mono (Subgroup.map_mono (inf_le_GammaH W H hHp))
    exact (CuspFormClass.zero_at_cusps F hc' γ hγ).boundedAtFilter

def gamma0SL : SL(2, ℤ) := ⟨!![W.a, W.b; (W.R : ℤ), (p : ℤ)], by
  rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

theorem alGL_eq : W.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (gamma0SL W) * ModularForm.heckeDiagMatrix p := by
  have hp : p ≠ 0 := W.q_pos.ne'
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.val_heckeDiagMatrix hp]
  show (W.mat).map (algebraMap ℤ ℝ) = ((gamma0SL W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) * !![(p : ℝ), 0; 0, 1]
  rw [ModularForm.AtkinLehnerDatum.mat]
  show _ = (!![W.a, W.b; (W.R : ℤ), (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) * !![(p : ℝ), 0; 0, 1]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, mul_comm]

theorem coe_intCast_Zbar (m : ℤ) : ((m : integralClosure ℤ ℂ) : ℂ) = (m : ℂ) := by simp

theorem intCast_notMem {𝔪 : Ideal (integralClosure ℤ ℂ)} (h𝔪 : 𝔪.IsPrime)
    (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪) (hp : p.Prime) {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) :
    (D : integralClosure ℤ ℂ) ∉ 𝔪 := by
  intro hDm
  have hcop : IsCoprime (p : ℤ) D := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hD
  obtain ⟨u, v, huv⟩ := hcop
  apply h𝔪.ne_top
  rw [Ideal.eq_top_iff_one]
  have : (1 : integralClosure ℤ ℂ) = (u : integralClosure ℤ ℂ) * (p : integralClosure ℤ ℂ)
      + (v : integralClosure ℤ ℂ) * (D : integralClosure ℤ ℂ) := by
    have := congrArg (Int.cast : ℤ → integralClosure ℤ ℂ) huv
    push_cast at this
    exact this.symm
  rw [this]
  exact 𝔪.add_mem (𝔪.mul_mem_left _ hp𝔪) (𝔪.mul_mem_left _ hDm)

theorem exists_eq_pow_mul_not_dvd (hp : p.Prime) {D : ℤ} (hD : D ≠ 0) :
    ∃ (v : ℕ) (D' : ℤ), D = (p : ℤ) ^ v * D' ∧ ¬ (p : ℤ) ∣ D' := by
  obtain ⟨v, n', hn', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hD) p hp.one_lt.ne'
  refine ⟨v, D.sign * n', ?_, ?_⟩
  · calc D = D.sign * (D.natAbs : ℤ) := (Int.sign_mul_natAbs D).symm
      _ = D.sign * ((p : ℤ) ^ v * n') := by rw [hn]; push_cast; ring
      _ = (p : ℤ) ^ v * (D.sign * n') := by ring
  · intro h
    apply hn'
    have h1 : (p : ℤ) ∣ D.sign * n' := h
    have hs : D.sign = 1 ∨ D.sign = -1 := by
      rcases lt_trichotomy D 0 with hlt | heq | hgt
      · exact Or.inr (Int.sign_eq_neg_one_of_neg hlt)
      · exact absurd heq hD
      · exact Or.inl (Int.sign_eq_one_of_pos hgt)
    rcases hs with hs | hs
    · rw [hs, one_mul] at h1; exact_mod_cast h1
    · rw [hs, neg_one_mul, dvd_neg] at h1; exact_mod_cast h1

theorem main (hpr : Fact p.Prime) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {k : ℤ} (hk : Even k) (F : CuspForm (CohCarrier.GammaH M H) k) (P : PowerSeries ℤ)
    (hF : IsIntegralQExp F P) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d F)) n := by
  have hp : p.Prime := hpr.out
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI : NeZero p := ⟨hp0⟩
  haveI : NeZero W.R := ⟨fun h => NeZero.ne M (by rw [W.hM, h, mul_zero])⟩
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0

  obtain ⟨X, hX⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp k (CuspForm.diamondLinH k d F)

  set σ : SL(2, ℤ) := ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)) with hσ
  set γ : SL(2, ℤ) := σ * gamma0SL W with hγdef
  have hσ0 : σ ∈ Gamma0 M := (CuspForm.gammaLift M d).2
  have hRM : W.R ∣ M := Dvd.intro_left p W.hM.symm
  have hγ : γ ∈ Gamma0 W.R := by
    refine (Gamma0 W.R).mul_mem ?_ ?_
    ·
      rw [Gamma0_mem] at hσ0 ⊢
      have : ((((σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M).cast : ZMod W.R) = 0 := by rw [hσ0]; simp
      rwa [ZMod.cast_intCast hRM] at this
    · rw [Gamma0_mem]
      show ((((gamma0SL W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod W.R) = 0
      show (((W.R : ℤ) : ℤ) : ZMod W.R) = 0
      simp
  have hγp : (p : ℤ) ∣ γ 1 1 := by
    have h10 : (M : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Gamma0_mem.mp hσ0
    have hpM : (p : ℤ) ∣ (M : ℤ) := by rw [W.hM_int]; exact Dvd.intro _ rfl
    show (p : ℤ) ∣ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * ((gamma0SL W : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    show (p : ℤ) ∣ (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * W.b + (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (p : ℤ)
    exact dvd_add ((hpM.trans h10).mul_right _) (Dvd.intro_left _ rfl)

  obtain ⟨D, p₁, hD, hint⟩ := ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even W.R p hk
    (restrict W H hHp F) hF γ hγ hγp

  set Φ : UpperHalfPlane → ℂ := fun τ => ((⇑F : UpperHalfPlane → ℂ) ∣[k] γ) (ModularForm.heckeDiagMatrix p • τ) with hΦ
  have hXΦ : (⇑X : UpperHalfPlane → ℂ) = ((p : ℂ) ^ (k - 1)) • Φ := by
    funext τ
    rw [hX, ModularForm.alSlash_def, CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k) d F,
      alGL_eq W, ← SlashAction.slash_mul, ← mul_assoc, ← map_mul, SlashAction.slash_mul,
      ModularForm.slash_heckeDiagMatrix_apply k hp0, Pi.smul_apply, smul_eq_mul]
    rfl

  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := T_mem_GammaH H
  have h1 : (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]; exact AddSubgroup.mem_zmultiples 1
  have hDΦ : ((D : ℂ) • Φ) = ((D : ℂ) * (p : ℂ) ^ (1 - k)) • (⇑X : UpperHalfPlane → ℂ) := by
    rw [hXΦ, smul_smul, mul_assoc, ← zpow_add₀ hpC, show (1 - k) + (k - 1) = 0 by ring, zpow_zero, mul_one]
  have hcoeff : ∀ n : ℕ, ((PowerSeries.coeff n p₁ : ℤ) : ℂ) = (D : ℂ) * (p : ℂ) ^ (1 - k) * qCoeff (⇑X) n := by
    intro n
    have h := hint.coeff n
    rw [show ((D : ℂ) • fun τ : UpperHalfPlane => ((⇑(restrict W H hHp F) : UpperHalfPlane → ℂ) ∣[k] γ)
        (ModularForm.heckeDiagMatrix p • τ)) = (D : ℂ) • Φ from rfl, hDΦ,
      ModularForm.qExpansion_smul one_pos h1 _ X] at h
    rw [h, qCoeff, PowerSeries.coeff_smul, smul_eq_mul]

  obtain ⟨v, D', hDD, hD'⟩ := exists_eq_pow_mul_not_dvd hp hD
  refine ⟨v + (1 - k).toNat, fun n => ⟨(((p : ℤ) ^ (k - 1).toNat * PowerSeries.coeff n p₁ : ℤ)), (D' : integralClosure ℤ ℂ),
    intCast_notMem h𝔪 hp𝔪 hp hD', ?_⟩⟩
  have hD'C : (D' : ℂ) ≠ 0 := by
    intro h0
    apply hD
    rw [hDD, show D' = 0 by exact_mod_cast h0, mul_zero]

  have hXn : qCoeff (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d F)) n = qCoeff (⇑X) n := by rw [hX]
  rw [hXn]
  have key : (D' : ℂ) * (p : ℂ) ^ (v + (1 - k).toNat) * qCoeff (⇑X) n
      = (p : ℂ) ^ (k - 1).toNat * ((PowerSeries.coeff n p₁ : ℤ) : ℂ) := by
    rw [hcoeff n, hDD]
    push_cast

    rw [← zpow_natCast (p : ℂ) (v + (1 - k).toNat), ← zpow_natCast (p : ℂ) v, ← zpow_natCast (p : ℂ) (k - 1).toNat]
    have e1 : (((v + (1 - k).toNat : ℕ)) : ℤ) = (v : ℤ) + ((1 - k).toNat : ℤ) := by push_cast; ring
    have e2 : (((k - 1).toNat : ℕ) : ℤ) + (1 - k) = (((1 - k).toNat : ℕ) : ℤ) := by
      have := Int.toNat_sub_toNat_neg (k - 1)
      have h' : -(k - 1) = 1 - k := by ring
      rw [h'] at this
      omega
    rw [e1, zpow_add₀ hpC]
    have : (p : ℂ) ^ ((k - 1).toNat : ℤ) = (p : ℂ) ^ (((1 - k).toNat : ℕ) : ℤ) * (p : ℂ) ^ (-(1 - k)) := by
      rw [← zpow_add₀ hpC]; congr 1; omega
    rw [this, zpow_neg]
    field_simp
  rw [coe_intCast_Zbar, coe_intCast_Zbar]
  push_cast
  linear_combination key.symm

end RES.WBDD
p2m_reactivate "P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp.RES P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp.RES.WBDD"
p2m_reactivate "P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp.RES"

end
p2m_reactivate "P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp.RES P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp.RES.WBDD"

open ModularFormClass RES.WBDD in
theorem solution
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {k : ℤ} (hk : Even k) (F : CuspForm (CohCarrier.GammaH M H) k) (P : PowerSeries ℤ) (hF : ModularCurve.IsIntegralQExp F P) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash W k ⇑(CuspForm.diamondLinH k d F)) n :=
  RES.WBDD.main W inferInstance H hHp d 𝔪 h𝔪 hp𝔪 hk F P hF

end S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp
end P2MW
export P2MW.S_CuspForm_exists_forall_qCoeff_alSlash_diamondLinH_p_integral_of_isIntegralQExp (solution)
