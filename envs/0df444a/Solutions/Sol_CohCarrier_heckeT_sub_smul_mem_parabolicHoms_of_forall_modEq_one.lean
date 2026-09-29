-- Prove2me | solution 1 for CohCarrier.heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/230aa96b-5dca-5d89-b0b6-94a000fd60fb

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_CuspSpace_normalFormCriterion
import Theorems.Thm_ModularCurve_CuspSpace_exists_normalForm
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup OnePoint
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "mem_Gamma0Upper GammaH GammaH_top H1 conjUpperMat conjUpperMat_apply_11 conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT index_GammaHUpper_of_prime"
namespace BoundaryEis
p2m_open "CohCarrier"

def unipMat (p q m : ℤ) : SL(2, ℤ) :=
  ⟨!![1 - m * p * q, m * p * p; -(m * q * q), 1 + m * p * q], by
    rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem unipMat_apply_00 (p q m : ℤ) : (unipMat p q m) 0 0 = 1 - m * p * q := rfl
@[scoped simp] theorem unipMat_apply_01 (p q m : ℤ) : (unipMat p q m) 0 1 = m * p * p := rfl
@[scoped simp] theorem unipMat_apply_10 (p q m : ℤ) : (unipMat p q m) 1 0 = -(m * q * q) := rfl
@[scoped simp] theorem unipMat_apply_11 (p q m : ℤ) : (unipMat p q m) 1 1 = 1 + m * p * q := rfl

theorem conj_T_zpow_eq_unipMat (δ : SL(2, ℤ)) (m : ℤ) :
    δ * ModularGroup.T ^ m * δ⁻¹ = unipMat (δ 0 0) (δ 1 0) m := by
  obtain ⟨M, hM⟩ := δ
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rwa [Matrix.det_fin_two] at hM
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.SL2_inv_expl, ModularGroup.coe_T_zpow m]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, unipMat]
  · linear_combination hdet
  · ring
  · ring
  · linear_combination hdet

theorem trace_unipMat (p q m : ℤ) : ((unipMat p q m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.trace_fin_two]
  simp [unipMat]

theorem unipMat_pow (δ : SL(2, ℤ)) (h : ℤ) (n : ℕ) :
    (unipMat (δ 0 0) (δ 1 0) h) ^ n = unipMat (δ 0 0) (δ 1 0) (h * n) := by
  rw [← conj_T_zpow_eq_unipMat, ← conj_T_zpow_eq_unipMat, conj_pow, ← zpow_natCast, ← _root_.zpow_mul]

theorem inv_mul_unipMat_mul (r δ : SL(2, ℤ)) (m : ℤ) :
    r⁻¹ * unipMat (δ 0 0) (δ 1 0) m * r = unipMat ((r⁻¹ * δ) 0 0) ((r⁻¹ * δ) 1 0) m := by
  rw [← conj_T_zpow_eq_unipMat, ← conj_T_zpow_eq_unipMat]
  group

theorem unipMat_mem_Gamma0_iff (N : ℕ) (p q m : ℤ) :
    unipMat p q m ∈ Gamma0 N ↔ (N : ℤ) ∣ m * q * q := by
  rw [Gamma0_mem, unipMat_apply_10, Int.cast_neg, neg_eq_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]

@[scoped simp] theorem conjUpperMat_apply_00 (ℓ : ℕ) (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 0 0 = A 0 0 := by
  simp [conjUpperMat]

@[scoped simp] theorem conjUpperMat_apply_01 (ℓ : ℕ) (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 0 1 = A 0 1 / ℓ := by
  simp [conjUpperMat]

theorem SL2_ext {A B : SL(2, ℤ)} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem conjUpperMat_unipMat_of_dvd_left (ℓ : ℕ) (hℓ : (ℓ : ℤ) ≠ 0) {p : ℤ} (hp : (ℓ : ℤ) ∣ p)
    (q m : ℤ) (h : (ℓ : ℤ) ∣ (unipMat p q m) 0 1) :
    conjUpperMat ℓ (unipMat p q m) h = unipMat (p / ℓ) q (m * ℓ) := by
  obtain ⟨p', rfl⟩ := hp
  have hp' : (ℓ : ℤ) * p' / ℓ = p' := Int.mul_ediv_cancel_left _ hℓ
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [conjUpperMat_apply_00, unipMat_apply_00, unipMat_apply_00, hp']; ring
  · rw [conjUpperMat_apply_01, unipMat_apply_01, unipMat_apply_01, hp',
      show m * ((ℓ : ℤ) * p') * ((ℓ : ℤ) * p') = ℓ * (m * ℓ * p' * p') by ring,
      Int.mul_ediv_cancel_left _ hℓ]
  · rw [conjUpperMat_apply_10, unipMat_apply_10, unipMat_apply_10]; ring
  · rw [conjUpperMat_apply_11, unipMat_apply_11, unipMat_apply_11, hp']; ring

theorem conjUpperMat_unipMat_of_dvd_exp (ℓ : ℕ) (hℓ : (ℓ : ℤ) ≠ 0) (p q : ℤ) {m : ℤ}
    (hm : (ℓ : ℤ) ∣ m) (h : (ℓ : ℤ) ∣ (unipMat p q m) 0 1) :
    conjUpperMat ℓ (unipMat p q m) h = unipMat p (ℓ * q) (m / ℓ) := by
  obtain ⟨m', rfl⟩ := hm
  have hm' : (ℓ : ℤ) * m' / ℓ = m' := Int.mul_ediv_cancel_left _ hℓ
  refine SL2_ext ?_ ?_ ?_ ?_
  · rw [conjUpperMat_apply_00, unipMat_apply_00, unipMat_apply_00, hm']; ring
  · rw [conjUpperMat_apply_01, unipMat_apply_01, unipMat_apply_01, hm',
      show (ℓ : ℤ) * m' * p * p = ℓ * (m' * p * p) by ring, Int.mul_ediv_cancel_left _ hℓ]
  · rw [conjUpperMat_apply_10, unipMat_apply_10, unipMat_apply_10, hm']; ring
  · rw [conjUpperMat_apply_11, unipMat_apply_11, unipMat_apply_11, hm']; ring

theorem conj_T_zpow_of_apply_10_eq_zero (τ : SL(2, ℤ)) (hτ : τ 1 0 = 0) (m : ℤ) :
    τ * ModularGroup.T ^ m * τ⁻¹ = ModularGroup.T ^ m := by
  rw [conj_T_zpow_eq_unipMat, hτ]
  have hdet : τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe τ
    rwa [Matrix.det_fin_two] at h
  rw [hτ, mul_zero, sub_zero] at hdet
  have hsq : τ 0 0 * τ 0 0 = 1 := Int.isUnit_mul_self (IsUnit.of_mul_eq_one _ hdet)
  ext i j
  rw [ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [unipMat]
  rw [mul_assoc, hsq, mul_one]

theorem exists_SL2_col {p q : ℤ} (h : IsCoprime p q) : ∃ σ : SL(2, ℤ), σ 0 0 = p ∧ σ 1 0 = q := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨!![p, -y; q, x], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination hxy

theorem isCoprime_col (δ : SL(2, ℤ)) : IsCoprime (δ 0 0) (δ 1 0) := by
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe δ
    rwa [Matrix.det_fin_two] at h
  exact ⟨δ 1 1, -(δ 0 1), by linear_combination hdet⟩

theorem exists_conj_of_mk_eq (N : ℕ) (σ₁ σ₂ : SL(2, ℤ))
    (h : ModularCurve.CuspSpace.mk N (mapGL ℚ σ₁ • (∞ : OnePoint ℚ)) =
      ModularCurve.CuspSpace.mk N (mapGL ℚ σ₂ • (∞ : OnePoint ℚ))) :
    ∃ g ∈ Gamma0 N, ∀ m : ℤ,
      σ₁ * ModularGroup.T ^ m * σ₁⁻¹ = g * (σ₂ * ModularGroup.T ^ m * σ₂⁻¹) * g⁻¹ := by
  obtain ⟨g, hg, hsmul⟩ := ModularCurve.CuspSpace.mk_eq_mk_iff.mp h
  refine ⟨g, hg, fun m => ?_⟩

  set τ : SL(2, ℤ) := σ₁⁻¹ * g * σ₂ with hτ
  have hfix : mapGL ℚ τ • (∞ : OnePoint ℚ) = ∞ := by
    rw [hτ, map_mul, map_mul, mul_smul, mul_smul, hsmul, ← mul_smul, ← map_mul, inv_mul_cancel,
      map_one, one_smul]
  have hτ10 : τ 1 0 = 0 := by
    rw [ModularCurve.mapGL_smul_infty, ModularCurve.ratPoint_eq_infty_iff] at hfix
    exact hfix
  have key := conj_T_zpow_of_apply_10_eq_zero τ hτ10 m
  have hg' : g = σ₁ * τ * σ₂⁻¹ := by rw [hτ]; group
  rw [hg']
  calc σ₁ * ModularGroup.T ^ m * σ₁⁻¹ = σ₁ * (τ * ModularGroup.T ^ m * τ⁻¹) * σ₁⁻¹ := by rw [key]
    _ = _ := by group

section Cusps

open ModularCurve ModularCurve.CuspSpace

variable {N : ℕ}

theorem eq_or_eq_neg_of_ratPoint_eq {a c a' c' : ℤ} (h : IsCoprime a c) (h' : IsCoprime a' c')
    (heq : ratPoint a c = ratPoint a' c') : (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hc' : c' = 0 := by
      rw [ratPoint_zero_right] at heq
      exact ratPoint_eq_infty_iff.mp heq.symm
    subst hc'
    have hu : IsUnit a := isCoprime_zero_right.mp h
    have hu' : IsUnit a' := isCoprime_zero_right.mp h'
    rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
        rcases Int.isUnit_iff.mp hu' with rfl | rfl <;>
      norm_num
  · have hc' : c' ≠ 0 := by
      intro h0
      rw [h0, ratPoint_zero_right, ratPoint_eq_infty_iff] at heq
      exact hc heq
    have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
    have hcQ' : (c' : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc'
    rw [ratPoint_of_ne_zero _ hc, ratPoint_of_ne_zero _ hc', OnePoint.coe_eq_coe,
      div_eq_div_iff hcQ hcQ'] at heq
    have hZ : a * c' = a' * c := by exact_mod_cast heq
    have h1 : c ∣ c' := h.symm.dvd_of_dvd_mul_left ⟨a', by linear_combination hZ⟩
    have h2 : c' ∣ c := h'.symm.dvd_of_dvd_mul_left ⟨a, by linear_combination -hZ⟩
    obtain ⟨u, hu⟩ := h1
    obtain ⟨v, hv⟩ := h2
    have huv : u * v = 1 := by
      have h3 : c * (u * v) = c * 1 := by rw [mul_one, ← mul_assoc, ← hu, ← hv]
      exact mul_left_cancel₀ hc h3
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one v huv) with hu1 | hu1
    · rw [hu1, mul_one] at hu
      rw [hu] at hZ
      exact Or.inl ⟨mul_right_cancel₀ hc hZ, hu.symm⟩
    · rw [hu1, mul_neg_one] at hu
      rw [hu] at hZ
      refine Or.inr ⟨?_, by rw [hu, neg_neg]⟩
      have : a * (-c) = (-a') * (-c) := by rw [hZ]; ring
      exact mul_right_cancel₀ (neg_ne_zero.mpr hc) this

theorem dvd_sub_mul_of_smul_eq_general {d n₁ : ℕ} (hd0 : ((d : ℕ) : ℤ) ≠ 0)
    (hem : ((d : ℕ) : ℤ) * ((n₁ : ℕ) : ℤ) = (N : ℤ)) {a c₁ a₀ ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N)
    (h0 : γ 0 0 * a + γ 0 1 * (((d : ℕ) : ℤ) * c₁) = ε * a₀)
    (h1 : γ 1 0 * a + γ 1 1 * (((d : ℕ) : ℤ) * c₁) = ε * ((d : ℕ) : ℤ)) :
    ((Nat.gcd d n₁ : ℕ) : ℤ) ∣ a₀ - a * c₁ := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ γ 1 0 := Gamma0_mem_iff_dvd.mp hγ
  have h2 : ε - γ 1 1 * c₁ = ((n₁ : ℕ) : ℤ) * k * a := by
    have h2' : ((d : ℕ) : ℤ) * (ε - γ 1 1 * c₁) = ((d : ℕ) : ℤ) * (((n₁ : ℕ) : ℤ) * k * a) := by
      linear_combination -h1 + a * hk - a * k * hem
    exact mul_left_cancel₀ hd0 h2'
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.property
    rwa [Matrix.det_fin_two] at h
  have h3 : ε * a₀ - γ 0 0 * a = γ 0 1 * (((d : ℕ) : ℤ) * c₁) := by linear_combination -h0
  have key : a₀ - a * c₁
      = ε * (γ 0 1 * (((d : ℕ) : ℤ) * c₁)) + γ 0 0 * a * (((n₁ : ℕ) : ℤ) * k * a)
        + a * c₁ * (γ 0 1 * γ 1 0) := by
    linear_combination ε * h3 + γ 0 0 * a * h2 + a * c₁ * hdet - a₀ * hε2
  have hgd : ((Nat.gcd d n₁ : ℕ) : ℤ) ∣ ((d : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left d n₁)
  have hgn : ((Nat.gcd d n₁ : ℕ) : ℤ) ∣ ((n₁ : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right d n₁)
  have hg10 : ((Nat.gcd d n₁ : ℕ) : ℤ) ∣ γ 1 0 := by
    rw [hk, ← hem]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgd _) k
  rw [key]
  exact dvd_add (dvd_add
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hgd c₁) (γ 0 1)) ε)
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hgn k) a) (γ 0 0 * a)))
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hg10 (γ 0 1)) (a * c₁))

theorem gcd_dvd_normalForm_numerator_sub (hN : N ≠ 0) {a c a₀ : ℤ} (hac : IsCoprime a c)
    (ha₀ : IsCoprime a₀ ((Int.gcd c (N : ℤ) : ℕ) : ℤ))
    (hmk : mk N (ratPoint a c) = mk N (ratPoint a₀ ((Int.gcd c (N : ℤ) : ℕ) : ℤ))) :
    ((Nat.gcd (Int.gcd c (N : ℤ)) (N / Int.gcd c (N : ℤ)) : ℕ) : ℤ) ∣
      a₀ - a * (c / ((Int.gcd c (N : ℤ) : ℕ) : ℤ)) := by
  have hcd : cuspDenom N (mk N (ratPoint a c)) = Int.gcd c (N : ℤ) := cuspDenom_mk_ratPoint hac
  have hdN : Int.gcd c (N : ℤ) ∣ N := by rw [← hcd]; exact cuspDenom_dvd _
  have hd0 : Int.gcd c (N : ℤ) ≠ 0 := fun h =>
    hN (by exact_mod_cast (Int.gcd_eq_zero_iff.mp h).2)
  have hd0' : ((Int.gcd c (N : ℤ) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hd0
  have hdc : ((Int.gcd c (N : ℤ) : ℕ) : ℤ) ∣ c := Int.gcd_dvd_left ..
  have hc₁ : ((Int.gcd c (N : ℤ) : ℕ) : ℤ) * (c / ((Int.gcd c (N : ℤ) : ℕ) : ℤ)) = c :=
    Int.mul_ediv_cancel' hdc
  have hem : ((Int.gcd c (N : ℤ) : ℕ) : ℤ) * ((N / Int.gcd c (N : ℤ) : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hdN
  obtain ⟨γ, hγ, hsmul⟩ := mk_eq_mk_iff.mp hmk.symm
  rw [mapGL_smul_ratPoint (a := a) (c := c) γ hac.ne_zero_or_ne_zero] at hsmul
  rcases eq_or_eq_neg_of_ratPoint_eq (isCoprime_smul_pair γ hac) ha₀ hsmul with
    ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact dvd_sub_mul_of_smul_eq_general (ε := 1) hd0' hem (Or.inl rfl) hγ
      (by rw [hc₁]; linear_combination h0) (by rw [hc₁]; linear_combination h1)
  · exact dvd_sub_mul_of_smul_eq_general (ε := -1) hd0' hem (Or.inr rfl) hγ
      (by rw [hc₁]; linear_combination h0) (by rw [hc₁]; linear_combination h1)

theorem mk_ratPoint_eq_of_invariants (hN : N ≠ 0) {a c a' c' : ℤ}
    (h : IsCoprime a c) (h' : IsCoprime a' c') (hdd' : Int.gcd c (N : ℤ) = Int.gcd c' (N : ℤ))
    (hcong : ((Nat.gcd (Int.gcd c (N : ℤ)) (N / Int.gcd c (N : ℤ)) : ℕ) : ℤ) ∣
        a' * (c' / ((Int.gcd c (N : ℤ) : ℕ) : ℤ)) - a * (c / ((Int.gcd c (N : ℤ) : ℕ) : ℤ))) :
    mk N (ratPoint a c) = mk N (ratPoint a' c') := by
  obtain ⟨a₀, ha₀, hx⟩ := exists_normalForm hN (mk N (ratPoint a c))
  obtain ⟨a₀', ha₀', hx'⟩ := exists_normalForm hN (mk N (ratPoint a' c'))
  have hcd : cuspDenom N (mk N (ratPoint a c)) = Int.gcd c (N : ℤ) := cuspDenom_mk_ratPoint h
  have hcd' : cuspDenom N (mk N (ratPoint a' c')) = Int.gcd c' (N : ℤ) := cuspDenom_mk_ratPoint h'
  rw [hcd] at hx ha₀
  rw [hcd'] at hx' ha₀'
  have hdN : Int.gcd c (N : ℤ) ∣ N := by rw [← hcd]; exact cuspDenom_dvd _
  have hA := gcd_dvd_normalForm_numerator_sub hN h ha₀ hx
  have hA' := gcd_dvd_normalForm_numerator_sub hN h' ha₀' hx'
  rw [← hdd'] at ha₀' hx' hA'
  have hcong₀ : ((Nat.gcd (Int.gcd c (N : ℤ)) (N / Int.gcd c (N : ℤ)) : ℕ) : ℤ) ∣ a₀' - a₀ := by
    have hT : a₀' - a₀ = (a₀' - a' * (c' / ((Int.gcd c (N : ℤ) : ℕ) : ℤ)))
        + (a' * (c' / ((Int.gcd c (N : ℤ) : ℕ) : ℤ)) - a * (c / ((Int.gcd c (N : ℤ) : ℕ) : ℤ)))
        - (a₀ - a * (c / ((Int.gcd c (N : ℤ) : ℕ) : ℤ))) := by ring
    rw [hT]
    exact dvd_sub (dvd_add hA' hcong) hA
  rw [hx, hx']
  exact (normalFormCriterion hN a₀ a₀' _ hdN ha₀ ha₀').mpr
    ((ZMod.intCast_eq_intCast_iff_dvd_sub a₀ a₀' _).mpr hcong₀)

end Cusps

section Transfer

variable (M : ℕ) (Hs : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]

def termOf (φ : H1 M Hs A) (x : ↥(GammaH M Hs)) (hx : x ∈ GammaHUpper M Hs ℓ) : A :=
  φ (Additive.ofMul (conjL M Hs ℓ ⟨x, hx⟩))

theorem termOf_congr (φ : H1 M Hs A) {x y : ↥(GammaH M Hs)} (hx : x ∈ GammaHUpper M Hs ℓ)
    (hy : y ∈ GammaHUpper M Hs ℓ) (h : x = y) : termOf M Hs ℓ φ x hx = termOf M Hs ℓ φ y hy := by
  subst h; rfl

theorem heckeT_apply_eq_sum_orbits (φ : H1 M Hs A) (u : ↥(GammaH M Hs))
    [Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u)
      (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)))] :
    heckeT M Hs ℓ A φ (Additive.ofMul u) =
      ∑ O : Quotient (MulAction.orbitRel (Subgroup.zpowers u)
          (↥(GammaH M Hs) ⧸ GammaHUpper M Hs ℓ)),
        termOf M Hs ℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
          (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out) := by
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M Hs ℓ)) u) = _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  rfl

theorem apply_conj (φ : H1 M Hs A) (g x : ↥(GammaH M Hs)) :
    φ (Additive.ofMul (g * x * g⁻¹)) = φ (Additive.ofMul x) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]; abel

theorem apply_inv_conj (φ : H1 M Hs A) (g x : ↥(GammaH M Hs)) :
    φ (Additive.ofMul (g⁻¹ * x * g)) = φ (Additive.ofMul x) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]; abel

theorem termOf_conj (φ : H1 M Hs A) {x k : ↥(GammaH M Hs)} (hx : x ∈ GammaHUpper M Hs ℓ)
    (hk : k ∈ GammaHUpper M Hs ℓ) (hkxk : k⁻¹ * x * k ∈ GammaHUpper M Hs ℓ) :
    termOf M Hs ℓ φ (k⁻¹ * x * k) hkxk = termOf M Hs ℓ φ x hx := by
  unfold termOf
  have : (⟨k⁻¹ * x * k, hkxk⟩ : ↥(GammaHUpper M Hs ℓ)) = ⟨k, hk⟩⁻¹ * ⟨x, hx⟩ * ⟨k, hk⟩ := rfl
  rw [this, (conjL M Hs ℓ).map_mul, (conjL M Hs ℓ).map_mul, (conjL M Hs ℓ).map_inv]
  exact apply_inv_conj M Hs φ _ _

end Transfer

section Main

variable {N : ℕ} {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem mem_GammaH_top_iff {x : SL(2, ℤ)} : x ∈ GammaH N ⊤ ↔ x ∈ Gamma0 N := by
  rw [GammaH_top]

theorem mem_GammaHUpper_iff {r : ↥(GammaH N ⊤)} :
    r ∈ GammaHUpper N ⊤ ℓ ↔ (ℓ : ℤ) ∣ (r : SL(2, ℤ)) 0 1 := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

def pOf (δ : SL(2, ℤ)) (r : ↥(GammaH N ⊤)) : ℤ := ((r : SL(2, ℤ))⁻¹ * δ) 0 0

def qOf (δ : SL(2, ℤ)) (r : ↥(GammaH N ⊤)) : ℤ := ((r : SL(2, ℤ))⁻¹ * δ) 1 0

theorem pOf_eq (δ : SL(2, ℤ)) (r : ↥(GammaH N ⊤)) :
    pOf δ r = (r : SL(2, ℤ)) 1 1 * δ 0 0 - (r : SL(2, ℤ)) 0 1 * δ 1 0 := by
  unfold pOf
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable (δ : SL(2, ℤ)) (h : ℤ) (u : ↥(GammaH N ⊤))
  (hu : (u : SL(2, ℤ)) = unipMat (δ 0 0) (δ 1 0) h)

include hu in

theorem coe_inv_mul_pow_mul (r : ↥(GammaH N ⊤)) (n : ℕ) :
    ((r⁻¹ * u ^ n * r : ↥(GammaH N ⊤)) : SL(2, ℤ)) = unipMat (pOf δ r) (qOf δ r) (h * n) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hu, unipMat_pow,
    inv_mul_unipMat_mul]
  rfl

include hu in
theorem inv_mul_pow_mul_mem_iff (r : ↥(GammaH N ⊤)) (n : ℕ) :
    r⁻¹ * u ^ n * r ∈ GammaHUpper N ⊤ ℓ ↔ (ℓ : ℤ) ∣ h * n * pOf δ r * pOf δ r := by
  rw [mem_GammaHUpper_iff, coe_inv_mul_pow_mul δ h u hu, unipMat_apply_01]

include hu in
theorem pow_smul_coe_eq_iff (r : ↥(GammaH N ⊤)) (n : ℕ) :
    u ^ n • ((r : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ)) = r ↔
      (ℓ : ℤ) ∣ h * n * pOf δ r * pOf δ r := by
  rw [← inv_mul_pow_mul_mem_iff δ h u hu, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    ← inv_mem_iff, _root_.mul_inv_rev, inv_inv]
  simp only [mul_assoc]

variable (hℓ : ℓ.Prime) (hδ : (ℓ : ℤ) ∣ δ 0 0)

include hℓ hδ in
theorem not_dvd_e : ¬ (ℓ : ℤ) ∣ δ 1 0 := by
  intro he
  have h1 : (ℓ : ℤ) ∣ 1 := by
    obtain ⟨x, y, hxy⟩ := isCoprime_col δ
    rw [← hxy]; exact dvd_add (dvd_mul_of_dvd_right hδ _) (dvd_mul_of_dvd_right he _)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hℓ.one_lt.ne' (by exact_mod_cast this)

include hℓ hδ in

theorem dvd_pOf_iff (r : ↥(GammaH N ⊤)) : (ℓ : ℤ) ∣ pOf δ r ↔ r ∈ GammaHUpper N ⊤ ℓ := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  rw [mem_GammaHUpper_iff, pOf_eq]
  constructor
  · intro hp
    have h2 : (ℓ : ℤ) ∣ (r : SL(2, ℤ)) 0 1 * δ 1 0 := by
      have := dvd_sub (dvd_mul_of_dvd_right hδ ((r : SL(2, ℤ)) 1 1)) hp
      rwa [sub_sub_cancel] at this
    exact (hprime.dvd_or_dvd h2).resolve_right (not_dvd_e δ hℓ hδ)
  · intro hr
    exact dvd_sub (dvd_mul_of_dvd_right hδ _) (dvd_mul_of_dvd_left hr _)

def m₀ (ℓ : ℕ) (h : ℤ) : ℕ := if (ℓ : ℤ) ∣ h then 1 else ℓ

theorem dvd_h_mul_m₀ : (ℓ : ℤ) ∣ h * (m₀ ℓ h : ℕ) := by
  unfold m₀
  split_ifs with hh
  · simpa using hh
  · exact dvd_mul_left _ _

include hu hℓ hδ in

theorem minimalPeriod_eq_m₀ (r : ↥(GammaH N ⊤)) (hr : r ∉ GammaHUpper N ⊤ ℓ) :
    Function.minimalPeriod (u • ·) ((r : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ)) = m₀ ℓ h := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  unfold m₀
  split_ifs with hh
  · rw [Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt]
    have := (pow_smul_coe_eq_iff (ℓ := ℓ) δ h u hu r 1).mpr (by
      simpa using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hh _) _)
    simpa using this
  · haveI : Fact ℓ.Prime := ⟨hℓ⟩
    apply Function.minimalPeriod_eq_prime
    · rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
      exact (pow_smul_coe_eq_iff (ℓ := ℓ) δ h u hu r ℓ).mpr
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
    · rw [Function.IsFixedPt]
      intro hfix
      have := (pow_smul_coe_eq_iff (ℓ := ℓ) δ h u hu r 1).mp (by simpa using hfix)
      simp only [Nat.cast_one, mul_one] at this
      rcases hprime.dvd_or_dvd this with h1 | h1
      · rcases hprime.dvd_or_dvd h1 with h2 | h2
        · exact hh h2
        · exact hp h2
      · exact hp h1

abbrev OrbQ (N ℓ : ℕ) (u : ↥(GammaH N ⊤)) : Type :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers u) (↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ))

def orbOne (N ℓ : ℕ) (u : ↥(GammaH N ⊤)) : OrbQ N ℓ u :=
  Quotient.mk _ (((1 : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ))

theorem orbOne_out (huK : u ∈ GammaHUpper N ⊤ ℓ) :
    (orbOne N ℓ u).out = (((1 : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ)) := by
  have hrel : (orbOne N ℓ u).out ∈ MulAction.orbit (Subgroup.zpowers u)
      (((1 : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ)) :=
    MulAction.orbitRel_apply.mp (Quotient.mk_out _)
  obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp hrel
  rw [← hz]
  change ((((z : ↥(GammaH N ⊤)) * 1 : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ)) = _
  rw [mul_one, QuotientGroup.eq, mul_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
  rw [← hk]
  exact inv_mem (Subgroup.zpow_mem _ huK k)

theorem orbOne_out_out_mem (huK : u ∈ GammaHUpper N ⊤ ℓ) :
    (orbOne N ℓ u).out.out ∈ GammaHUpper N ⊤ ℓ := by
  have h1 : (((orbOne N ℓ u).out.out : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ) =
      ((1 : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ) := by
    rw [QuotientGroup.out_eq', orbOne_out u huK]
  have := QuotientGroup.eq.mp h1.symm
  rwa [inv_one, one_mul] at this

theorem eq_orbOne_of_mem (O : OrbQ N ℓ u) (hO : O.out.out ∈ GammaHUpper N ⊤ ℓ) : O = orbOne N ℓ u := by
  have h1 : O.out = ((1 : ↥(GammaH N ⊤)) : ↥(GammaH N ⊤) ⧸ GammaHUpper N ⊤ ℓ) := by
    rw [← QuotientGroup.out_eq' O.out]
    symm
    exact QuotientGroup.eq.mpr (by rwa [inv_one, one_mul])
  rw [← Quotient.out_eq O, h1]
  rfl

theorem minimalPeriod_orbOne_out (huK : u ∈ GammaHUpper N ⊤ ℓ) :
    Function.minimalPeriod (u • ·) (orbOne N ℓ u).out = 1 := by
  rw [orbOne_out u huK, Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt,
    MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
  exact inv_mem huK

variable (hℓN : ¬ ℓ ∣ N) (hℓ1 : ∀ t : ℕ, t * t ∣ N → ℓ ≡ 1 [MOD t])

include hℓ hℓN in
theorem N_ne_zero : N ≠ 0 := by rintro rfl; exact hℓN (dvd_zero ℓ)

include hℓ hℓN hℓ1 in

theorem gcd_dvd_ell_sub_one (q : ℤ) :
    ((Nat.gcd (Int.gcd q (N : ℤ)) (N / Int.gcd q (N : ℤ)) : ℕ) : ℤ) ∣ (ℓ : ℤ) - 1 := by
  set c : ℕ := Int.gcd q (N : ℤ) with hc
  have hcN : c ∣ N := by
    have := Int.gcd_dvd_right q (N : ℤ)
    exact Int.natCast_dvd_natCast.mp this
  have htt : Nat.gcd c (N / c) * Nat.gcd c (N / c) ∣ N := by
    calc Nat.gcd c (N / c) * Nat.gcd c (N / c) ∣ c * (N / c) :=
          Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      _ = N := Nat.mul_div_cancel' hcN
  have := (Nat.modEq_iff_dvd.mp (hℓ1 _ htt).symm)
  simpa using this

include hℓ hℓN hℓ1 in

theorem mk_ratPoint_div_eq {a e : ℤ} (hae : IsCoprime a e) (ha : (ℓ : ℤ) ∣ a) :
    ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint a e) =
      ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint (a / ℓ) e) := by
  obtain ⟨a', rfl⟩ := ha
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  rw [Int.mul_ediv_cancel_left _ hℓ0]
  refine mk_ratPoint_eq_of_invariants (N_ne_zero hℓ hℓN) hae hae.of_mul_left_right rfl ?_
  have ht := gcd_dvd_ell_sub_one hℓ hℓN hℓ1 e
  rw [show a' * (e / ((Int.gcd e (N : ℤ) : ℕ) : ℤ)) - (ℓ : ℤ) * a' * (e / ((Int.gcd e (N : ℤ) : ℕ) : ℤ)) =
    ((ℓ : ℤ) - 1) * (-(a' * (e / ((Int.gcd e (N : ℤ) : ℕ) : ℤ)))) by ring]
  exact dvd_mul_of_dvd_left ht _

include hℓ hℓN hℓ1 in

theorem mk_ratPoint_mul_eq {p q : ℤ} (hpq : IsCoprime p q) (hp : IsCoprime p (ℓ * q)) :
    ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint p q) =
      ModularCurve.CuspSpace.mk N (ModularCurve.ratPoint p (ℓ * q)) := by
  have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN
  have hdd' : Int.gcd q (N : ℤ) = Int.gcd ((ℓ : ℤ) * q) (N : ℤ) := by
    show Nat.gcd q.natAbs _ = Nat.gcd ((ℓ : ℤ) * q).natAbs _
    rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast, Nat.Coprime.gcd_mul_left_cancel _ hcop]
  refine mk_ratPoint_eq_of_invariants (N_ne_zero hℓ hℓN) hpq hp hdd' ?_
  have ht := gcd_dvd_ell_sub_one hℓ hℓN hℓ1 q
  have hcq : ((Int.gcd q (N : ℤ) : ℕ) : ℤ) ∣ q := Int.gcd_dvd_left ..
  rw [Int.mul_ediv_assoc _ hcq,
    show p * ((ℓ : ℤ) * (q / ((Int.gcd q (N : ℤ) : ℕ) : ℤ))) - p * (q / ((Int.gcd q (N : ℤ) : ℕ) : ℤ)) =
      ((ℓ : ℤ) - 1) * (p * (q / ((Int.gcd q (N : ℤ) : ℕ) : ℤ))) by ring]
  exact dvd_mul_of_dvd_left ht _

theorem conjUpperMat_congr {X Y : SL(2, ℤ)} (hXY : X = Y) (hX : (ℓ : ℤ) ∣ X 0 1) (hY : (ℓ : ℤ) ∣ Y 0 1) :
    conjUpperMat ℓ X hX = conjUpperMat ℓ Y hY := by
  subst hXY; rfl

theorem coe_conjL (x : ↥(GammaHUpper N ⊤ ℓ)) :
    ((conjL N ⊤ ℓ x : ↥(GammaH N ⊤)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH N ⊤)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper N ⊤ ℓ x) := rfl

include hu hδ in
theorem u_mem_upper : u ∈ GammaHUpper N ⊤ ℓ := by
  rw [mem_GammaHUpper_iff, hu, unipMat_apply_01]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _

include hu in
theorem N_dvd : (N : ℤ) ∣ h * δ 1 0 * δ 1 0 := by
  have := u.2
  rw [mem_GammaH_top_iff, hu, unipMat_mem_Gamma0_iff] at this
  exact this

include hu hℓ hδ hℓN hℓ1 in

theorem termOf_u (φ : H1 N ⊤ A) :
    termOf N ⊤ ℓ φ u (u_mem_upper δ h u hu hδ) = ℓ • φ (Additive.ofMul u) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hae : IsCoprime (δ 0 0) (δ 1 0) := isCoprime_col δ
  have ha'e : IsCoprime (δ 0 0 / ℓ) (δ 1 0) := by
    obtain ⟨a', ha'⟩ := hδ
    rw [ha', Int.mul_ediv_cancel_left _ hℓ0]
    rw [ha'] at hae
    exact hae.of_mul_left_right
  obtain ⟨σ₂, hσ00, hσ10⟩ := exists_SL2_col ha'e

  have hval : ((conjL N ⊤ ℓ ⟨u, u_mem_upper δ h u hu hδ⟩ : ↥(GammaH N ⊤)) : SL(2, ℤ)) =
      σ₂ * ModularGroup.T ^ (h * ℓ) * σ₂⁻¹ := by
    rw [coe_conjL, conj_T_zpow_eq_unipMat, hσ00, hσ10]
    rw [conjUpperMat_congr hu (dvd_of_mem_GammaHUpper N ⊤ ℓ ⟨u, u_mem_upper δ h u hu hδ⟩)
      (by rw [unipMat_apply_01]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _)]
    exact conjUpperMat_unipMat_of_dvd_left ℓ hℓ0 hδ _ _ _

  have hmk : ModularCurve.CuspSpace.mk N (mapGL ℚ δ • (∞ : OnePoint ℚ)) =
      ModularCurve.CuspSpace.mk N (mapGL ℚ σ₂ • (∞ : OnePoint ℚ)) := by
    rw [ModularCurve.mapGL_smul_infty, ModularCurve.mapGL_smul_infty, hσ00, hσ10]
    exact mk_ratPoint_div_eq hℓ hℓN hℓ1 hae hδ
  obtain ⟨g, hg, hconj⟩ := exists_conj_of_mk_eq N δ σ₂ hmk
  set g' : ↥(GammaH N ⊤) := ⟨g, mem_GammaH_top_iff.mpr hg⟩ with hg'
  have hpow : ((u ^ ℓ : ↥(GammaH N ⊤)) : SL(2, ℤ)) = δ * ModularGroup.T ^ (h * ℓ) * δ⁻¹ := by
    rw [Subgroup.coe_pow, hu, unipMat_pow, conj_T_zpow_eq_unipMat]
  have hkey : conjL N ⊤ ℓ ⟨u, u_mem_upper δ h u hu hδ⟩ = g'⁻¹ * u ^ ℓ * g' := by
    apply Subtype.ext
    rw [hval, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hpow, hconj (h * ℓ), hg']
    group
  unfold termOf
  rw [hkey, apply_inv_conj, ofMul_pow, map_nsmul]

def m₁ (ℓ : ℕ) (h : ℤ) : ℤ := h * (m₀ ℓ h : ℕ) / ℓ

include hℓ in
theorem m₁_mul : m₁ ℓ h * ℓ = h * (m₀ ℓ h : ℕ) := by
  unfold m₁
  exact Int.ediv_mul_cancel (dvd_h_mul_m₀ h)

include hu hℓ hℓN in
theorem uStar_mem : unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h) ∈ GammaH N ⊤ := by
  rw [mem_GammaH_top_iff, unipMat_mem_Gamma0_iff]
  have hN := N_dvd δ h u hu
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  unfold m₁ m₀
  split_ifs with hh
  · obtain ⟨h', rfl⟩ := hh
    simp only [Nat.cast_one, mul_one, Int.mul_ediv_cancel_left _ hℓ0]
    have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [show (ℓ : ℤ) * (h' * δ 1 0 * δ 1 0) = (ℓ : ℤ) * h' * δ 1 0 * δ 1 0 by ring]
    exact hN
  · rwa [Int.mul_ediv_cancel _ hℓ0]

def uStar (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : ↥(GammaH N ⊤) :=
  ⟨unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h), uStar_mem δ h u hu hℓ hℓN⟩

include hδ hℓ1 in

theorem termOf_other (φ : H1 N ⊤ A) (r : ↥(GammaH N ⊤)) (hr : r ∉ GammaHUpper N ⊤ ℓ)
    (hmem : r⁻¹ * u ^ (m₀ ℓ h) * r ∈ GammaHUpper N ⊤ ℓ) :
    termOf N ⊤ ℓ φ (r⁻¹ * u ^ (m₀ ℓ h) * r) hmem = φ (Additive.ofMul (uStar δ h u hu hℓ hℓN)) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  have hpq : IsCoprime (pOf δ r) (qOf δ r) := isCoprime_col _
  have hpℓq : IsCoprime (pOf δ r) ((ℓ : ℤ) * qOf δ r) :=
    IsCoprime.mul_right ((Prime.coprime_iff_not_dvd hprime).mpr hp).symm hpq
  obtain ⟨σ₁, hσ00, hσ10⟩ := exists_SL2_col hpℓq
  have hval : ((conjL N ⊤ ℓ ⟨_, hmem⟩ : ↥(GammaH N ⊤)) : SL(2, ℤ)) =
      σ₁ * ModularGroup.T ^ (m₁ ℓ h) * σ₁⁻¹ := by
    rw [coe_conjL, conj_T_zpow_eq_unipMat, hσ00, hσ10]
    rw [conjUpperMat_congr (coe_inv_mul_pow_mul δ h u hu r (m₀ ℓ h))
      (dvd_of_mem_GammaHUpper N ⊤ ℓ ⟨_, hmem⟩)
      (by rw [unipMat_apply_01]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_h_mul_m₀ h) _) _)]
    exact conjUpperMat_unipMat_of_dvd_exp ℓ hℓ0 _ _ (dvd_h_mul_m₀ h) _
  have hr0 : ((r : ↥(GammaH N ⊤)) : SL(2, ℤ)) ∈ Gamma0 N := mem_GammaH_top_iff.mp r.2
  have hmk : ModularCurve.CuspSpace.mk N (mapGL ℚ δ • (∞ : OnePoint ℚ)) =
      ModularCurve.CuspSpace.mk N (mapGL ℚ σ₁ • (∞ : OnePoint ℚ)) := by
    rw [ModularCurve.mapGL_smul_infty σ₁, hσ00, hσ10, ← mk_ratPoint_mul_eq hℓ hℓN hℓ1 hpq hpℓq]
    unfold pOf qOf
    rw [← ModularCurve.mapGL_smul_infty, map_mul, mul_smul, ModularCurve.CuspSpace.mk_smul (inv_mem hr0)]
  obtain ⟨g, hg, hconj⟩ := exists_conj_of_mk_eq N δ σ₁ hmk
  set g' : ↥(GammaH N ⊤) := ⟨g, mem_GammaH_top_iff.mpr hg⟩ with hg'
  have hkey : conjL N ⊤ ℓ ⟨_, hmem⟩ = g'⁻¹ * uStar δ h u hu hℓ hℓN * g' := by
    apply Subtype.ext
    rw [hval, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg']
    show _ = g⁻¹ * unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h) * g
    rw [← conj_T_zpow_eq_unipMat, hconj (m₁ ℓ h)]
    group
  unfold termOf
  rw [hkey, apply_inv_conj]

include hu hℓ hδ hℓN hℓ1 in

theorem heckeT_apply_u (φ : H1 N ⊤ A) :
    heckeT N ⊤ ℓ A φ (Additive.ofMul u) = (ℓ + 1) • φ (Additive.ofMul u) := by
  classical
  haveI : Fintype (OrbQ N ℓ u) := Fintype.ofFinite _
  have huK := u_mem_upper δ h u hu hδ
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hper : ∀ O : OrbQ N ℓ u, O ≠ orbOne N ℓ u →
      Function.minimalPeriod (u • ·) O.out = m₀ ℓ h := by
    intro O hO
    have hr : O.out.out ∉ GammaHUpper N ⊤ ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have := minimalPeriod_eq_m₀ δ h u hu hℓ hδ O.out.out hr
    rwa [QuotientGroup.out_eq'] at this

  have hterm : ∀ O : OrbQ N ℓ u, O ≠ orbOne N ℓ u →
      termOf N ⊤ ℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
        (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out) =
      φ (Additive.ofMul (uStar δ h u hu hℓ hℓN)) := by
    intro O hO
    have hr : O.out.out ∉ GammaHUpper N ⊤ ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have hmem : O.out.out⁻¹ * u ^ (m₀ ℓ h) * O.out.out ∈ GammaHUpper N ⊤ ℓ := by
      have := QuotientGroup.out_conj_pow_minimalPeriod_mem (GammaHUpper N ⊤ ℓ) u O.out
      rwa [hper O hO] at this
    rw [termOf_congr N ⊤ ℓ φ _ hmem (by rw [hper O hO])]
    exact termOf_other δ h u hu hℓ hδ hℓN hℓ1 φ O.out.out hr hmem

  have hone : termOf N ⊤ ℓ φ ((orbOne N ℓ u).out.out⁻¹ *
      u ^ Function.minimalPeriod (u • ·) (orbOne N ℓ u).out * (orbOne N ℓ u).out.out)
      (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u _) = ℓ • φ (Additive.ofMul u) := by
    have hr := orbOne_out_out_mem u huK
    have hmem : (orbOne N ℓ u).out.out⁻¹ * u * (orbOne N ℓ u).out.out ∈ GammaHUpper N ⊤ ℓ :=
      mul_mem (mul_mem (inv_mem hr) huK) hr
    rw [termOf_congr N ⊤ ℓ φ _ hmem (by rw [minimalPeriod_orbOne_out u huK, pow_one]),
      termOf_conj N ⊤ ℓ φ huK hr hmem]
    exact termOf_u δ h u hu hℓ hδ hℓN hℓ1 φ

  have hidx : ℓ + 1 = ∑ O : OrbQ N ℓ u, Function.minimalPeriod (u • ·) O.out := by
    rw [← index_GammaHUpper_of_prime N ⊤ ℓ hℓ hℓN]
    exact Subgroup.index_eq_sum_minimalPeriod _ u
  rw [Finset.sum_eq_add_sum_sdiff_singleton (orbOne N ℓ u) _ (fun h => (h (Finset.mem_univ _)).elim),
    minimalPeriod_orbOne_out u huK, Finset.sum_congr rfl (fun O hO => hper O (by simpa using hO)),
    Finset.sum_const, smul_eq_mul, add_comm, Nat.add_left_cancel_iff] at hidx

  rw [heckeT_apply_eq_sum_orbits,
    Finset.sum_eq_add_sum_sdiff_singleton (orbOne N ℓ u) _ (fun h => (h (Finset.mem_univ _)).elim),
    hone, Finset.sum_congr rfl (fun O hO => hterm O (by simpa using hO)), Finset.sum_const, succ_nsmul]
  congr 1
  by_cases hh : (ℓ : ℤ) ∣ h
  · have hm₀ : m₀ ℓ h = 1 := by simp [m₀, hh]
    rw [hm₀, mul_one] at hidx
    rw [← hidx, ← map_nsmul, ← ofMul_pow]
    congr 2
    apply Subtype.ext
    rw [Subgroup.coe_pow, hu]
    show unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h) ^ ℓ = _
    rw [unipMat_pow, m₁_mul h hℓ, hm₀, Nat.cast_one, mul_one]
  · have hm₀ : m₀ ℓ h = ℓ := by simp [m₀, hh]
    rw [hm₀, eq_comm, mul_eq_right₀ hℓ.ne_zero] at hidx
    rw [hidx, one_smul]
    congr 2
    apply Subtype.ext
    rw [hu]
    show unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h) = _
    rw [m₁, hm₀, Int.mul_ediv_cancel _ hℓ0]

end Main

section Assembly

variable {N : ℕ} {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A]
  (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ∀ t : ℕ, t * t ∣ N → ℓ ≡ 1 [MOD t])

include hℓ hℓN in

theorem exists_mul_dvd (δ : SL(2, ℤ)) : ∃ g ∈ Gamma0 N, (ℓ : ℤ) ∣ (g * δ) 0 0 := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  by_cases he : (ℓ : ℤ) ∣ δ 1 0
  ·
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)
    refine ⟨⟨!![(ℓ : ℤ), -y; (N : ℤ), x], by rw [Matrix.det_fin_two_of]; linear_combination hxy⟩,
      by rw [Gamma0_mem]; simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right he _)
  ·
    obtain ⟨x, z, hxz⟩ := (Prime.coprime_iff_not_dvd hprime).mpr he
    refine ⟨ModularGroup.T ^ (-(δ 0 0 * z)), by
      rw [Gamma0_mem, ModularGroup.coe_T_zpow]; simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
    exact ⟨δ 0 0 * x, by linear_combination (-(δ 0 0)) * hxz⟩

include hℓ hℓN hℓ1 in

theorem heckeT_apply_parabolic (φ : H1 N ⊤ A) (δ : SL(2, ℤ)) (h : ℤ) (u : ↥(GammaH N ⊤))
    (hu : (u : SL(2, ℤ)) = δ * ModularGroup.T ^ h * δ⁻¹) :
    heckeT N ⊤ ℓ A φ (Additive.ofMul u) = (ℓ + 1) • φ (Additive.ofMul u) := by
  obtain ⟨g, hg, hdvd⟩ := exists_mul_dvd hℓ hℓN δ
  set g' : ↥(GammaH N ⊤) := ⟨g, mem_GammaH_top_iff.mpr hg⟩ with hg'
  set u' : ↥(GammaH N ⊤) := g' * u * g'⁻¹ with hu'def
  have hu' : (u' : SL(2, ℤ)) = unipMat ((g * δ) 0 0) ((g * δ) 1 0) h := by
    rw [hu'def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu, hg', ← conj_T_zpow_eq_unipMat]
    group
  have key := heckeT_apply_u (g * δ) h u' hu' hℓ hdvd hℓN hℓ1 φ
  rwa [hu'def, apply_conj, apply_conj] at key

theorem conjUpperMat_neg_one (hn : (ℓ : ℤ) ∣ (-1 : SL(2, ℤ)) 0 1) : conjUpperMat ℓ (-1) hn = -1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [conjUpperMat, Matrix.SpecialLinearGroup.coe_neg]

include hℓ hℓN in

theorem heckeT_apply_neg_one (φ : H1 N ⊤ A) (ε : ↥(GammaH N ⊤)) (hε : (ε : SL(2, ℤ)) = -1) :
    heckeT N ⊤ ℓ A φ (Additive.ofMul ε) = (ℓ + 1) • φ (Additive.ofMul ε) := by
  have hcomm : ∀ x : ↥(GammaH N ⊤), Commute ε x := fun x => by
    show ε * x = x * ε
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hε, neg_one_mul, mul_neg_one]
  have key : ∀ (k : ℕ) (g₀ : ↥(GammaH N ⊤)), g₀⁻¹ * ε ^ k * g₀ ∈ GammaHUpper N ⊤ ℓ →
      g₀⁻¹ * ε ^ k * g₀ = ε ^ k := fun k g₀ _ => by
    rw [mul_assoc, ((hcomm g₀).pow_left k).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hεK : ε ∈ GammaHUpper N ⊤ ℓ := by
    rw [mem_GammaHUpper_iff, hε, Matrix.SpecialLinearGroup.coe_neg]
    simp
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N ⊤ ℓ)) ε) = _
  rw [MonoidHom.transfer_eq_pow _ ε key]
  have hpow : (⟨ε ^ (GammaHUpper N ⊤ ℓ).index, MonoidHom.transfer_eq_pow_aux ε key⟩ :
      ↥(GammaHUpper N ⊤ ℓ)) = ⟨ε, hεK⟩ ^ (ℓ + 1) := by
    apply Subtype.ext
    simp [index_GammaHUpper_of_prime N ⊤ ℓ hℓ hℓN]
  have hfix : conjL N ⊤ ℓ ⟨ε, hεK⟩ = ε := by
    apply Subtype.ext
    rw [coe_conjL]
    show conjUpperMat ℓ (ε : SL(2, ℤ)) _ = _
    rw [conjUpperMat_congr hε _ (by rw [Matrix.SpecialLinearGroup.coe_neg]; simp), conjUpperMat_neg_one, hε]
  rw [hpow, map_pow, MonoidHom.comp_apply, hfix, toAdd_pow]
  rfl

include hℓ hℓN hℓ1 in

theorem heckeT_apply_of_trace_sq (φ : H1 N ⊤ A) (γ : ↥(GammaH N ⊤))
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    heckeT N ⊤ ℓ A φ (Additive.ofMul γ) = (ℓ + 1) • φ (Additive.ofMul γ) := by
  obtain ⟨ε, δ, h, hε, hγeq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
  have hεmem : ε ∈ GammaH N ⊤ := by
    rw [mem_GammaH_top_iff, Gamma0_mem]
    rcases hε with rfl | rfl
    · simp
    · rw [Matrix.SpecialLinearGroup.coe_neg]; simp
  set ε' : ↥(GammaH N ⊤) := ⟨ε, hεmem⟩ with hε'
  set u : ↥(GammaH N ⊤) := ε'⁻¹ * γ with hudef
  have hu : (u : SL(2, ℤ)) = δ * ModularGroup.T ^ h * δ⁻¹ := by
    rw [hudef, Subgroup.coe_mul, Subgroup.coe_inv, hγeq, hε']
    group
  have hγu : γ = ε' * u := by rw [hudef]; group
  have hεT : heckeT N ⊤ ℓ A φ (Additive.ofMul ε') = (ℓ + 1) • φ (Additive.ofMul ε') := by
    rcases hε with h1 | h1
    · have : ε' = 1 := Subtype.ext h1
      rw [this, ofMul_one, map_zero, map_zero, smul_zero]
    · exact heckeT_apply_neg_one hℓ hℓN φ ε' h1
  rw [hγu, ofMul_mul, map_add, map_add, hεT, heckeT_apply_parabolic hℓ hℓN hℓ1 φ δ h u hu, smul_add]

end Assembly

end CohCarrier.BoundaryEis
p2m_reactivate "P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one.CohCarrier P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one.CohCarrier.BoundaryEis"
p2m_reactivate "P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one.CohCarrier"

open CohCarrier.BoundaryEis in
theorem solution (N : ℕ) (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (hℓ1 : ∀ t : ℕ, t * t ∣ N → ℓ ≡ 1 [MOD t]) :
    CohCarrier.heckeT N ⊤ ℓ A φ - (ℓ + 1) • φ ∈
      ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N ⊤) A := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff]
  intro γ hγ
  rw [AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply, sub_eq_zero]
  exact heckeT_apply_of_trace_sq hℓ hℓN hℓ1 φ γ hγ

end S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one
end P2MW
export P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_of_forall_modEq_one (solution)
