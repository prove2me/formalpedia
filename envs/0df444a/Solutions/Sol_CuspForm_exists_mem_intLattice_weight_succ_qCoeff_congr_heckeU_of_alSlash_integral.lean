-- Prove2me | solution 1 for CuspForm.exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9fedb6fd-3b47-5cec-a845-62d655c408d5

import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_exists_coe_eq_add_smul_heckeU_alSlash
import Theorems.Thm_ModularCurve_StarBank_eisInt_series
import Theorems.Thm_ModularCurve_StarBank_eisInt_not_dvd_num
import Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
import Theorems.Thm_ModularForm_alSlash_alSlash
import Theorems.Thm_ModularForm_alSlash_mul
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_CuspForm_exists_coe_eq_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral

set_option autoImplicit false

open UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm

noncomputable section

namespace WLA5

section al
variable {M q : ℕ} (A : ModularForm.AtkinLehnerDatum M q)

private def gam0 : SL(2, ℤ) :=
  ⟨!![A.a, A.b; (A.R : ℤ), (q : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination A.bezout⟩

@[scoped simp] private lemma gam0_coe : ((gam0 A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![A.a, A.b; (A.R : ℤ), (q : ℤ)] := rfl

private lemma alGL_eq [NeZero M] :
    A.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (gam0 A) * ModularForm.heckeDiagMatrix q := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.val_heckeDiagMatrix hq0]
  change _ = ((gam0 A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) * _
  rw [gam0_coe, ModularForm.AtkinLehnerDatum.mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma alSlash_levelOne_apply [NeZero M] {k : ℤ} (E : ModularForm 𝒮ℒ k) (τ : UpperHalfPlane) :
    ModularForm.alSlash A k ⇑E τ = (q : ℂ) ^ (k - 1) * E (ModularForm.heckeDiagMatrix q • τ) := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  have hmem : Matrix.SpecialLinearGroup.mapGL ℝ (gam0 A) ∈ 𝒮ℒ := ⟨gam0 A, rfl⟩
  rw [ModularForm.alSlash_def, alGL_eq, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn E _ hmem, ModularForm.slash_heckeDiagMatrix_apply k hq0]

private lemma coeff_qExpansion_alSlash_levelOne [NeZero M] {k : ℤ} (E : ModularForm 𝒮ℒ k)
    (EM : ModularForm (CongruenceSubgroup.Gamma0 M) k) (hEM : (⇑EM : UpperHalfPlane → ℂ) = ⇑E) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (ModularForm.alSlash A k ⇑EM)) =
      (q : ℂ) ^ (k - 1) * (if q ∣ n then PowerSeries.coeff (n / q) (qExpansion 1 ⇑E) else 0) := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  have hqpos : 0 < q := A.q_pos
  have h1M : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h1S : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by simp
  haveI : Fact (IsCusp OnePoint.infty 𝒮ℒ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1S⟩
  have hEW : (⇑(ModularForm.atkinLehnerLin A k EM) : UpperHalfPlane → ℂ) = ModularForm.alSlash A k ⇑EM := rfl
  rw [← hEW]
  symm
  refine ModularFormClass.qExpansion_coeff_unique one_pos h1M (f := ModularForm.atkinLehnerLin A k EM)
    (c := fun n => (q : ℂ) ^ (k - 1) * (if q ∣ n then PowerSeries.coeff (n / q) (qExpansion 1 ⇑E) else 0))
    (fun τ => ?_) n
  rw [show (ModularForm.atkinLehnerLin A k EM) τ = ModularForm.alSlash A k ⇑EM τ from rfl, hEM,
    alSlash_levelOne_apply A E τ]
  have hsum := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex E h1S) (holo E)
    (bdd_at_infty E) (ModularForm.heckeDiagMatrix q • τ)
  have hq : Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix q • τ : UpperHalfPlane) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
    rw [ModularForm.coe_heckeDiagMatrix_smul hq0 τ]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq] at hsum
  have hsupp : ∀ x ∉ Set.range (fun m : ℕ => q * m),
      (fun j : ℕ => ((q : ℂ) ^ (k - 1) * (if q ∣ j then PowerSeries.coeff (j / q) (qExpansion 1 ⇑E) else 0)) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ j) x = 0 := by
    intro x hx
    have : ¬ q ∣ x := fun ⟨m, hm⟩ => hx ⟨m, hm.symm⟩
    simp [this]
  refine ((mul_right_injective₀ hq0).hasSum_iff hsupp).mp ?_
  convert hsum.mul_left ((q : ℂ) ^ (k - 1)) using 1
  all_goals
    ext m
    simp only [Function.comp_apply, Nat.mul_div_cancel_left _ hqpos, dvd_mul_right, if_true, pow_mul, smul_eq_mul]
    try ring

end al

private def IsIntPS (φ : PowerSeries ℂ) : Prop := ∃ ψ : PowerSeries ℤ, ψ.map (Int.castRingHom ℂ) = φ

namespace IsIntPS

private lemma add {φ χ : PowerSeries ℂ} (h₁ : IsIntPS φ) (h₂ : IsIntPS χ) : IsIntPS (φ + χ) := by
  obtain ⟨ψ, rfl⟩ := h₁
  obtain ⟨ω, rfl⟩ := h₂
  exact ⟨ψ + ω, map_add _ _ _⟩

private lemma intCast_mul {φ : PowerSeries ℂ} (h : IsIntPS φ) (z : ℤ) : IsIntPS ((z : PowerSeries ℂ) * φ) := by
  obtain ⟨ψ, rfl⟩ := h
  exact ⟨(z : PowerSeries ℤ) * ψ, by rw [map_mul, map_intCast]⟩

private lemma of_coeff {φ : PowerSeries ℂ} (h : ∀ n, ∃ m : ℤ, PowerSeries.coeff n φ = (m : ℂ)) : IsIntPS φ := by
  choose m hm using h
  exact ⟨PowerSeries.mk m, by ext n; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast, hm]⟩

end IsIntPS

section lattice
variable (N : ℕ) (k : ℤ)

private lemma one_mem_strictPeriods_Gamma0' :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

private def qExpHom : CuspForm (CongruenceSubgroup.Gamma0 N) k →+ PowerSeries ℂ where
  toFun f := qExpansion 1 ⇑f
  map_zero' := by
    show qExpansion 1 ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) = 0
    rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]
  map_add' f g := by
    show qExpansion 1 ⇑(f + g) = qExpansion 1 ⇑f + qExpansion 1 ⇑g
    rw [CuspForm.coe_add]
    exact qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0' N))
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos (one_mem_strictPeriods_Gamma0' N))

private lemma qExpHom_apply (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : qExpHom N k f = qExpansion 1 ⇑f := rfl

variable {N k} in

private theorem isIntPS_of_mem_intLattice {f : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hf : f ∈ CuspForm.intLattice N k) :
    IsIntPS (qExpansion 1 ⇑f) := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact IsIntPS.of_coeff hx
  | zero => exact ⟨0, by rw [map_zero, CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]⟩
  | add x y _ _ hx hy =>
    rw [← qExpHom_apply, map_add, qExpHom_apply, qExpHom_apply]
    exact hx.add hy
  | smul z x _ hx =>
    rw [← qExpHom_apply, map_zsmul, qExpHom_apply, zsmul_eq_mul]
    exact hx.intCast_mul z

end lattice

private theorem a5_main (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2)
    (c : ℕ) (hc : c + 2 ≤ p)
    (hfW : ∀ n : ℕ, ∃ m : ℤ, (p : ℂ) ^ c * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ)) :
    ∃ g ∈ CuspForm.intLattice A.R ((p : ℤ) + 1), ∀ n : ℕ, ∃ m : ℤ,
      ModularFormClass.qCoeff g n - ModularFormClass.qCoeff (ModularForm.heckeU 2 p ⇑f) n = (p : ℂ) * m := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  have hp2 : p ≠ 2 := by omega
  haveI : NeZero A.R := ⟨A.R_pos.ne'⟩
  have hpM : p ∣ M := ⟨A.R, A.hM⟩
  have h1M : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h1R : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 A.R : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have ha3 : 3 ≤ p - 1 := by omega
  have ha2 : Even (p - 1) := hp.even_sub_one hp2
  have hk : (2 : ℤ) + ((p - 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by
    rw [Nat.cast_sub hp.one_le]; push_cast; ring

  obtain ⟨T, hTmap, hT0, hTdvd⟩ := ModularCurve.StarBank.eisInt_series (ℓ := p) hp5 ha3
  have hnump : ¬ (p : ℤ) ∣ (bernoulli (p - 1)).num := ModularCurve.StarBank.eisInt_not_dvd_num (ℓ := p) hp5
  set num : ℤ := (bernoulli (p - 1)).num with hnum
  set E : ModularForm 𝒮ℒ ((p - 1 : ℕ) : ℤ) := ModularForm.E ha3 with hEdef
  obtain ⟨EM, hEM⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne M E
  let Et : ModularForm (CongruenceSubgroup.Gamma0 M) ((p - 1 : ℕ) : ℤ) := (num : ℂ) • EM
  have hEtcoe : (⇑Et : ℍ → ℂ) = (num : ℂ) • ⇑EM := by rw [ModularForm.IsGLPos.coe_smul]
  have hEtq : qExpansion 1 ⇑Et = T.map (Int.castRingHom ℂ) := by
    rw [hEtcoe, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero EM one_pos h1M), hEM, hTmap]

  obtain ⟨T', hT'⟩ : ∃ T' : PowerSeries ℤ, T = PowerSeries.C num + PowerSeries.C (p : ℤ) * T' := by
    choose t ht using fun m : ℕ => hTdvd (m + 1) (Nat.succ_pos m)
    refine ⟨PowerSeries.X * PowerSeries.mk t, ?_⟩
    ext m
    rcases m with _ | m
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hT0]
      simp
    · rw [map_add, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero m), zero_add, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, ← ht m]

  let F : CuspForm (CongruenceSubgroup.Gamma0 M) (2 + ((p - 1 : ℕ) : ℤ)) := f.mulModularForm Et
  have hFcoe : (⇑F : ℍ → ℂ) = ⇑f * ⇑Et := rfl
  have hFq : qExpansion 1 ⇑F = qExpansion 1 ⇑f * T.map (Int.castRingHom ℂ) := by
    rw [hFcoe, ModularForm.qExpansion_mul_coe one_pos h1M f Et, hEtq]

  let FW : CuspForm (CongruenceSubgroup.Gamma0 M) (2 + ((p - 1 : ℕ) : ℤ)) :=
    CuspForm.atkinLehnerLin A (2 + ((p - 1 : ℕ) : ℤ)) F
  have hFWcoe : (⇑FW : ℍ → ℂ) = ModularForm.alSlash A (2 + ((p - 1 : ℕ) : ℤ)) ⇑F := rfl
  obtain ⟨G0, hG0⟩ := CuspForm.exists_coe_eq_add_smul_heckeU_alSlash p hp A (2 + ((p - 1 : ℕ) : ℤ)) FW

  have hFinv : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)),
      (⇑F : ℍ → ℂ) ∣[2 + ((p - 1 : ℕ) : ℤ)] γ = ⇑F :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ
  have hG0' : (⇑G0 : ℍ → ℂ) = ⇑FW + ModularForm.heckeU (2 + ((p - 1 : ℕ) : ℤ)) p ⇑F := by
    rw [hG0, hFWcoe, ModularForm.alSlash_alSlash A _ hFinv, ModularForm.heckeU_smul, smul_smul, ← zpow_add₀ hpC,
      show (2 : ℤ) - (2 + ((p - 1 : ℕ) : ℤ)) + (2 + ((p - 1 : ℕ) : ℤ) - 2) = 0 by ring, zpow_zero, one_smul]

  let fW : CuspForm (CongruenceSubgroup.Gamma0 M) 2 := CuspForm.atkinLehnerLin A 2 f
  have hfWcoe : (⇑fW : ℍ → ℂ) = ModularForm.alSlash A 2 ⇑f := rfl
  let EW : ModularForm (CongruenceSubgroup.Gamma0 M) ((p - 1 : ℕ) : ℤ) :=
    ModularForm.atkinLehnerLin A ((p - 1 : ℕ) : ℤ) Et
  have hEWcoe : (⇑EW : ℍ → ℂ) = ModularForm.alSlash A ((p - 1 : ℕ) : ℤ) ⇑Et := rfl
  have hmulcoe : (⇑(fW.mulModularForm EW) : ℍ → ℂ) = ⇑fW * ⇑EW := rfl
  have hFW : (⇑FW : ℍ → ℂ) = (p : ℂ) • ⇑(fW.mulModularForm EW) := by
    rw [hmulcoe, hFWcoe, hFcoe, ModularForm.alSlash_mul A 2 ((p - 1 : ℕ) : ℤ) ⇑f ⇑Et, hfWcoe, hEWcoe]

  let V : PowerSeries ℤ := PowerSeries.mk fun n => if p ∣ n then PowerSeries.coeff (n / p) T else 0
  have hTcoeff : ∀ j, ((PowerSeries.coeff j T : ℤ) : ℂ) = (num : ℂ) * PowerSeries.coeff j (qExpansion 1 ⇑E) := by
    intro j
    have := congrArg (fun S : PowerSeries ℂ => PowerSeries.coeff j S) hTmap
    rw [PowerSeries.coeff_map, eq_intCast, map_smul, smul_eq_mul] at this
    exact this
  have hpz : (p : ℂ) ^ (((p - 1 : ℕ) : ℤ) - 1) = (p : ℂ) ^ (p - 2) := by
    rw [← zpow_natCast, Nat.cast_sub (by omega : 2 ≤ p), Nat.cast_sub hp.one_le]
    norm_num
    ring_nf
  have hEWq : qExpansion 1 ⇑EW = PowerSeries.C ((p : ℂ) ^ (p - 2)) * V.map (Int.castRingHom ℂ) := by
    have hEMWcoe : (⇑(ModularForm.atkinLehnerLin A ((p - 1 : ℕ) : ℤ) EM) : ℍ → ℂ)
        = ModularForm.alSlash A ((p - 1 : ℕ) : ℤ) ⇑EM := rfl
    ext n
    rw [hEWcoe, hEtcoe, ModularForm.alSlash_smul, ← hEMWcoe,
      qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero (ModularForm.atkinLehnerLin A _ EM) one_pos h1M),
      map_smul, smul_eq_mul, hEMWcoe, coeff_qExpansion_alSlash_levelOne A E EM hEM n, hpz, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map, PowerSeries.coeff_mk]
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, if_pos hpn, eq_intCast, hTcoeff]; ring
    · rw [if_neg hpn, if_neg hpn, map_zero]; ring

  obtain ⟨Φ, hΦ⟩ := isIntPS_of_mem_intLattice hf
  obtain ⟨Ψ, hΨ⟩ : IsIntPS (PowerSeries.C ((p : ℂ) ^ c) * qExpansion 1 ⇑fW) :=
    IsIntPS.of_coeff fun n => by
      obtain ⟨m, hm⟩ := hfW n
      exact ⟨m, by rw [PowerSeries.coeff_C_mul, hfWcoe]; exact hm⟩
  have hfWq : qExpansion 1 ⇑fW = PowerSeries.C (((p : ℂ) ^ c)⁻¹) * Ψ.map (Int.castRingHom ℂ) := by
    rw [hΨ, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero c hpC), map_one, one_mul]
  have hpow : (p : ℂ) * ((p : ℂ) ^ c)⁻¹ * (p : ℂ) ^ (p - 2) = (p : ℂ) ^ (p - 1 - c) := by
    have h : (p : ℂ) ^ (p - 1 - c) * (p : ℂ) ^ c = (p : ℂ) * (p : ℂ) ^ (p - 2) := by
      rw [← pow_add, ← pow_succ', show p - 1 - c + c = p - 2 + 1 by omega]
    calc (p : ℂ) * ((p : ℂ) ^ c)⁻¹ * (p : ℂ) ^ (p - 2)
        = ((p : ℂ) ^ (p - 1 - c) * (p : ℂ) ^ c) * ((p : ℂ) ^ c)⁻¹ := by rw [h]; ring
      _ = (p : ℂ) ^ (p - 1 - c) := mul_inv_cancel_right₀ (pow_ne_zero c hpC) _
  have hFWq : qExpansion 1 ⇑FW = PowerSeries.C ((p : ℂ) ^ (p - 1 - c)) * (Ψ * V).map (Int.castRingHom ℂ) := by
    rw [hFW, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero (fW.mulModularForm EW) one_pos h1M),
      hmulcoe, ModularForm.qExpansion_mul_coe one_pos h1M fW EW, hfWq, hEWq, PowerSeries.smul_eq_C_mul, ← hpow,
      map_mul, map_mul, map_mul]
    ring
  have hFq' : qExpansion 1 ⇑F = PowerSeries.C (num : ℂ) * Φ.map (Int.castRingHom ℂ) +
      PowerSeries.C (p : ℂ) * (Φ * T').map (Int.castRingHom ℂ) := by
    rw [hFq, ← hΦ, hT', map_add, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C, eq_intCast, eq_intCast,
      Int.cast_natCast]
    ring

  obtain ⟨Uf, hUf⟩ := CuspForm.exists_coe_eq_heckeU F hpM
  have hUq : ∀ n, PowerSeries.coeff n (qExpansion 1 (ModularForm.heckeU (2 + ((p - 1 : ℕ) : ℤ)) p ⇑F)) =
      PowerSeries.coeff (n * p) (qExpansion 1 ⇑F) := by
    intro n
    have := ModularFormClass.qCoeff_heckeU F h1M hp0 n
    rw [ModularForm.coeffHeckeU_apply] at this
    exact this
  have hG0q : ∀ n, PowerSeries.coeff n (qExpansion 1 ⇑G0) =
      PowerSeries.coeff n (qExpansion 1 ⇑FW) + PowerSeries.coeff (n * p) (qExpansion 1 ⇑F) := by
    intro n
    rw [hG0', ← hUf, qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero FW one_pos h1M)
      (ModularFormClass.analyticAt_cuspFunction_zero Uf one_pos h1M), map_add, hUf, hUq]
  have hkey : ∀ n, ∃ z : ℤ, PowerSeries.coeff n (qExpansion 1 ⇑G0) =
      (num : ℂ) * PowerSeries.coeff (n * p) (Φ.map (Int.castRingHom ℂ)) + (p : ℂ) * z := by
    intro n
    refine ⟨(p : ℤ) ^ (p - 2 - c) * PowerSeries.coeff n (Ψ * V) + PowerSeries.coeff (n * p) (Φ * T'), ?_⟩
    rw [hG0q, hFWq, hFq', show p - 1 - c = (p - 2 - c) + 1 by omega, pow_succ]
    simp only [PowerSeries.coeff_C_mul, map_add, PowerSeries.coeff_map, eq_intCast]
    push_cast
    ring
  have hUf2 : ∀ n, qCoeff (ModularForm.heckeU 2 p ⇑f) n = PowerSeries.coeff (n * p) (Φ.map (Int.castRingHom ℂ)) := by
    intro n
    have := ModularFormClass.qCoeff_heckeU f h1M hp0 n
    rw [ModularForm.coeffHeckeU_apply] at this
    rw [this, hΦ]
    rfl

  obtain ⟨u, d, hud⟩ : IsCoprime (p : ℤ) num :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hnump
  have hud' : (u : ℂ) * p + d * num = 1 := by exact_mod_cast hud
  let G : CuspForm (CongruenceSubgroup.Gamma0 A.R) ((p : ℤ) + 1) := (d : ℂ) • CuspForm.mcast hk G0
  have hGcoe : (⇑G : ℍ → ℂ) = (d : ℂ) • ⇑G0 := by
    rw [CuspForm.IsGLPos.coe_smul]
    rfl
  have hGq : ∀ n, qCoeff (⇑G) n = (d : ℂ) * PowerSeries.coeff n (qExpansion 1 ⇑G0) := by
    intro n
    show PowerSeries.coeff n (qExpansion 1 ⇑G) = _
    rw [hGcoe, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero G0 one_pos h1R), map_smul,
      smul_eq_mul]
  refine ⟨G, Submodule.subset_span fun n => ?_, fun n => ?_⟩
  · obtain ⟨z, hz⟩ := hkey n
    refine ⟨d * (num * PowerSeries.coeff (n * p) Φ + p * z), ?_⟩
    rw [hGq, hz, PowerSeries.coeff_map, eq_intCast]
    push_cast
    ring
  · obtain ⟨z, hz⟩ := hkey n
    refine ⟨d * z - u * PowerSeries.coeff (n * p) Φ, ?_⟩
    rw [hGq, hz, hUf2, PowerSeries.coeff_map, eq_intCast]
    push_cast
    linear_combination ((PowerSeries.coeff (n * p) Φ : ℤ) : ℂ) * hud'

end WLA5
p2m_reactivate "P2MW.S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral.WLA5"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {M : ℕ} [NeZero M] (A : ModularForm.AtkinLehnerDatum M p)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f ∈ CuspForm.intLattice M 2)
    (c : ℕ) (hc : c + 2 ≤ p)
    (hfW : ∀ n : ℕ, ∃ m : ℤ, (p : ℂ) ^ c * ModularFormClass.qCoeff (ModularForm.alSlash A 2 ⇑f) n = (m : ℂ)) :
    ∃ g ∈ CuspForm.intLattice A.R ((p : ℤ) + 1), ∀ n : ℕ, ∃ m : ℤ,
      ModularFormClass.qCoeff g n - ModularFormClass.qCoeff (ModularForm.heckeU 2 p ⇑f) n = (p : ℂ) * m :=
  WLA5.a5_main p hp5 A f hf c hc hfW

end
p2m_reactivate "P2MW.S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral.WLA5"

end S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral
end P2MW
export P2MW.S_CuspForm_exists_mem_intLattice_weight_succ_qCoeff_congr_heckeU_of_alSlash_integral (solution)
