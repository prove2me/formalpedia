-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5742aae7-7502-5cc7-a259-3572ad603839

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul

open ModularForm Complex
p2m_open "UpperHalfPlane~I"

namespace RB1T

local notation "𝕢" => Function.Periodic.qParam

lemma sum_range_rootOfUnity_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    ∑ j ∈ Finset.range p, (cexp (2 * Real.pi * I / p) ^ m) ^ j
      = if p ∣ m then (p : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (cexp (2 * Real.pi * I / p)) p := Complex.isPrimitiveRoot_exp p hp
  split_ifs with hdvd
  · have h1 : cexp (2 * Real.pi * I / p) ^ m = 1 := (hζ.pow_eq_one_iff_dvd m).mpr hdvd
    simp [h1]
  · have h1 : cexp (2 * Real.pi * I / p) ^ m ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd m).mp h)
    rw [geom_sum_eq h1, pow_right_comm, hζ.pow_eq_one, one_pow, sub_self, zero_div]

lemma qParam_heckeMatrix_pow {p : ℕ} (hp : p ≠ 0) (j : ℕ) (τ : ℍ) (m : ℕ) :
    𝕢 1 ((heckeMatrix p j • τ : ℍ) : ℂ) ^ m
      = cexp (2 * Real.pi * I * τ * m / p) * (cexp (2 * Real.pi * I / p) ^ m) ^ j := by
  rw [coe_heckeMatrix_smul hp j τ]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul, ← pow_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma qParam_one_pow (τ : ℍ) (n : ℕ) :
    𝕢 1 (τ : ℂ) ^ n = cexp (2 * Real.pi * I * τ * n) := by
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem hasSum_heckeU {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) (k : ℤ) {p : ℕ} (hp : p ≠ 0)
    (τ : ℍ) :
    HasSum (fun n ↦ a (n * p) * 𝕢 1 τ ^ n) (heckeU k p F τ) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  set ζ : ℂ := cexp (2 * Real.pi * I / p) with hζdef
  set X : ℕ → ℂ := fun m ↦ cexp (2 * Real.pi * I * τ * m / p) with hXdef

  have h1 : ∀ j ∈ Finset.range p,
      HasSum (fun m ↦ a m * (X m * (ζ ^ m) ^ j)) (F (heckeMatrix p j • τ)) := by
    intro j _
    have := hF (heckeMatrix p j • τ)
    simpa only [qParam_heckeMatrix_pow hp j τ] using this

  have h2 : HasSum (fun m ↦ ∑ j ∈ Finset.range p, a m * (X m * (ζ ^ m) ^ j))
      (∑ j ∈ Finset.range p, F (heckeMatrix p j • τ)) := hasSum_sum h1
  have h3 : (fun m ↦ ∑ j ∈ Finset.range p, a m * (X m * (ζ ^ m) ^ j))
      = fun m ↦ a m * X m * (if p ∣ m then (p : ℂ) else 0) := by
    funext m
    rw [← sum_range_rootOfUnity_pow hp m, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3] at h2
  have h4 := h2.mul_left ((p : ℂ)⁻¹)
  rw [← heckeU_apply k hp F τ] at h4

  have hinj : Function.Injective (fun n : ℕ ↦ n * p) := mul_left_injective₀ hp
  have hvan : ∀ m ∉ Set.range (fun n : ℕ ↦ n * p),
      (fun m ↦ (p : ℂ)⁻¹ * (a m * X m * (if p ∣ m then (p : ℂ) else 0))) m = 0 := by
    intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, by simp [mul_comm]⟩
    simp [hndvd]
  have h5 := (hinj.hasSum_iff hvan).mpr h4
  convert h5 using 1
  funext n
  simp only [Function.comp_apply, Dvd.intro_left n rfl, if_true, hXdef]
  rw [qParam_one_pow, Nat.cast_mul, mul_div_assoc, mul_div_cancel_right₀ _ hp']
  field_simp

theorem hasSum_heckeDiag {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    HasSum (fun n ↦ (if p ∣ n then a (n / p) else 0) * 𝕢 1 τ ^ n) (F (heckeDiagMatrix p • τ)) := by
  have hinj : Function.Injective (fun n : ℕ ↦ n * p) := mul_left_injective₀ hp
  have hvan : ∀ m ∉ Set.range (fun n : ℕ ↦ n * p),
      (fun n ↦ (if p ∣ n then a (n / p) else 0) * 𝕢 1 τ ^ n) m = 0 := by
    intro m hm
    have hndvd : ¬ p ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, by simp [mul_comm]⟩
    simp [hndvd]
  refine (hinj.hasSum_iff hvan).mp ?_
  convert hF (heckeDiagMatrix p • τ) using 1
  funext m
  simp only [Function.comp_apply, Dvd.intro_left m rfl, if_true, Nat.mul_div_cancel _
    (Nat.pos_of_ne_zero hp)]
  congr 1
  rw [coe_heckeDiagMatrix_smul hp τ, qParam_one_pow]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_heckeT {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasSum (fun m ↦ a m * 𝕢 1 τ ^ m) (F τ)) (k : ℤ) {p : ℕ} (hp : p ≠ 0)
    (τ : ℍ) :
    HasSum (fun n ↦ coeffHeckeT k p a n * 𝕢 1 τ ^ n) (heckeT k p F τ) := by
  have hU := hasSum_heckeU hF k hp τ
  have hD := (hasSum_heckeDiag hF hp τ).mul_left ((p : ℂ) ^ (k - 1))
  rw [heckeT, Pi.add_apply, slash_heckeDiagMatrix_apply k hp]
  convert hU.add hD using 1
  funext n
  rw [coeffHeckeT_apply]
  split_ifs <;> ring

lemma hasSum_qCoeff {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    HasSum (fun m ↦ ModularFormClass.qCoeff f m * 𝕢 1 τ ^ m) (f τ) := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  haveI : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  simp only [smul_eq_mul] at this
  exact this

lemma qCoeff_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularFormClass.qCoeff f 0 = 0 := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  exact CuspFormClass.qExpansion_coeff_zero f one_pos h1

theorem coeffHeckeT_qCoeff_eq {N : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    coeffHeckeT 2 ℓ (fun m ↦ ModularFormClass.qCoeff f m) n
      = ModularFormClass.qCoeff f ℓ * ModularFormClass.qCoeff f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeffHeckeT_apply, qCoeff_zero]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn ℓ hℓ.one_lt.ne'
  have hcop : ∀ s : ℕ, (ℓ ^ s).Coprime m := fun s =>
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm)
  cases r with
  | zero =>

    have hndvd : ¬ ℓ ∣ ℓ ^ 0 * m := by simpa using hm
    rw [coeffHeckeT_of_not_dvd _ hndvd, pow_zero, one_mul,
      hf.qCoeff_mul_of_coprime m ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm).symm, mul_comm]
  | succ s =>
    have hdvd : ℓ ∣ ℓ ^ (s + 1) * m := Dvd.dvd.mul_right (dvd_pow_self ℓ (Nat.succ_ne_zero s)) m
    rw [coeffHeckeT_of_dvd _ hdvd,
      show ℓ ^ (s + 1) * m * ℓ = ℓ ^ (s + 2) * m by ring,
      show ℓ ^ (s + 1) * m / ℓ = ℓ ^ s * m by
        rw [pow_succ, mul_assoc, mul_comm ℓ, ← mul_assoc, Nat.mul_div_cancel _ hℓ.pos],
      hf.qCoeff_mul_of_coprime _ _ (hcop _), hf.qCoeff_mul_of_coprime _ _ (hcop _),
      hf.qCoeff_mul_of_coprime _ _ (hcop _), hf.qCoeff_prime_pow_of_not_dvd ℓ s hℓ hℓN]
    have h21 : ((2 : ℤ) - 1) = 1 := by norm_num
    rw [h21, zpow_one]
    ring

end RB1T

theorem solution (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    CuspForm.heckeTLin 2 hℓ hℓN f = ModularFormClass.qCoeff f ℓ • f := by
  refine DFunLike.ext _ _ fun τ => ?_
  rw [CuspForm.heckeTLin_apply_apply, CuspForm.IsGLPos.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hT := RB1T.hasSum_heckeT (RB1T.hasSum_qCoeff f) 2 hℓ.ne_zero τ
  have hS := (RB1T.hasSum_qCoeff f τ).mul_left (ModularFormClass.qCoeff f ℓ)
  refine hT.unique ?_
  convert hS using 1 <;> try rfl
  funext n
  rw [RB1T.coeffHeckeT_qCoeff_eq hf hℓ hℓN n, mul_assoc]

end S_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul (solution)
