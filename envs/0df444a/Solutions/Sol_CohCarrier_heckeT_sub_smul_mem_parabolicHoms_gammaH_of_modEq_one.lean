-- Prove2me | solution 1 for CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6b7ec96c-ce36-5698-9cab-01d017296cea

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "mem_Gamma0Upper gamma0Units GammaH mem_GammaH_iff H1 conjUpperMat conjUpperMat_apply_11 conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT uMat uMat_mem_GammaH index_GammaHUpper_of_prime"
namespace BoundaryEisH
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

theorem sign_comm {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (X : SL(2, ℤ)) : ε * X = X * ε := by
  rcases hε with rfl | rfl
  · rw [one_mul, mul_one]
  · rw [neg_one_mul, mul_neg_one]

theorem sign_pow_eq_or {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (n : ℕ) : ε ^ n = 1 ∨ ε ^ n = -1 := by
  rcases hε with rfl | rfl
  · exact Or.inl (one_pow n)
  · exact neg_one_pow_eq_or _ n

theorem sign_sq {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with rfl | rfl
  · rw [one_mul]
  · rw [neg_mul_neg, one_mul]

theorem sign_mul_apply_01 {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (X : SL(2, ℤ)) :
    (ε * X) 0 1 = X 0 1 ∨ (ε * X) 0 1 = -(X 0 1) := by
  rcases hε with rfl | rfl
  · left; rw [one_mul]
  · right; rw [neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]

theorem dvd_sign_mul_apply_01_iff {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (X : SL(2, ℤ)) (d : ℤ) :
    d ∣ (ε * X) 0 1 ↔ d ∣ X 0 1 := by
  rcases sign_mul_apply_01 hε X with h | h
  · rw [h]
  · rw [h, dvd_neg]

theorem conjUpperMat_sign_mul (ℓ : ℕ) {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (X : SL(2, ℤ))
    (h : (ℓ : ℤ) ∣ (ε * X) 0 1) (h' : (ℓ : ℤ) ∣ X 0 1) :
    conjUpperMat ℓ (ε * X) h = ε * conjUpperMat ℓ X h' := by
  have key1 : ∀ (Y : SL(2, ℤ)) (hY : (ℓ : ℤ) ∣ Y 0 1) (hXY : Y = X),
      conjUpperMat ℓ Y hY = conjUpperMat ℓ X h' := by
    intro Y hY hXY; subst hXY; rfl
  have key2 : ∀ (Y : SL(2, ℤ)) (hY : (ℓ : ℤ) ∣ Y 0 1) (hXY : Y = -X),
      conjUpperMat ℓ Y hY = -conjUpperMat ℓ X h' := by
    intro Y hY hXY; subst hXY
    refine SL2_ext ?_ ?_ ?_ ?_ <;>
      simp [conjUpperMat, Matrix.SpecialLinearGroup.coe_neg, Int.neg_ediv_of_dvd h']
  rcases hε with rfl | rfl
  · exact (key1 _ h (one_mul X)).trans (one_mul _).symm
  · exact (key2 _ h (neg_one_mul X)).trans (neg_one_mul _).symm

theorem sign_conj_left {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (k X : SL(2, ℤ)) :
    k * (ε * X) * k⁻¹ = ε * (k * X * k⁻¹) := by
  rcases hε with rfl | rfl
  · rw [one_mul, one_mul]
  · rw [neg_one_mul, neg_one_mul, mul_neg, neg_mul]

theorem sign_conj_inv {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (k X : SL(2, ℤ)) :
    k⁻¹ * (ε * X) * k = ε * (k⁻¹ * X * k) := by
  rcases hε with rfl | rfl
  · rw [one_mul, one_mul]
  · rw [neg_one_mul, neg_one_mul, mul_neg, neg_mul]

theorem sign_pow_succ_eq_one_iff {ε : SL(2, ℤ)} (hε : ε = 1 ∨ ε = -1) (ℓ : ℕ) (hεℓ : ε ^ (ℓ + 1) = 1) :
    ε ^ ℓ = ε := by
  have h1 : ε ^ (ℓ + 1) = ε ^ ℓ * ε := pow_succ ε ℓ
  rw [hεℓ] at h1
  calc ε ^ ℓ = ε ^ ℓ * (ε * ε) := by rw [sign_sq hε, mul_one]
    _ = 1 * ε := by rw [← mul_assoc, ← h1]
    _ = ε := one_mul ε

theorem exists_conj_of_col_congr (N : ℕ) (σ₁ σ₂ : SL(2, ℤ))
    (h0 : ((σ₁ 0 0 : ℤ) : ZMod N) = σ₂ 0 0) (h1 : ((σ₁ 1 0 : ℤ) : ZMod N) = σ₂ 1 0) :
    ∃ g ∈ Gamma N, ∀ m : ℤ,
      σ₁ * ModularGroup.T ^ m * σ₁⁻¹ = g * (σ₂ * ModularGroup.T ^ m * σ₂⁻¹) * g⁻¹ := by
  set τ : SL(2, ℤ) := σ₂⁻¹ * σ₁ with hτ
  have hdet₂ : σ₂ 0 0 * σ₂ 1 1 - σ₂ 0 1 * σ₂ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe σ₂; rwa [Matrix.det_fin_two] at h
  have hτ00 : τ 0 0 = σ₂ 1 1 * σ₁ 0 0 - σ₂ 0 1 * σ₁ 1 0 := by
    rw [hτ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hτ10 : τ 1 0 = -(σ₂ 1 0) * σ₁ 0 0 + σ₂ 0 0 * σ₁ 1 0 := by
    rw [hτ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hτdet : τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe τ; rwa [Matrix.det_fin_two] at h
  have c00 : ((τ 0 0 : ℤ) : ZMod N) = 1 := by
    rw [hτ00]; push_cast; rw [h0, h1]
    have := congrArg (fun z : ℤ => (z : ZMod N)) hdet₂
    push_cast at this
    linear_combination this
  have c10 : ((τ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [hτ10]; push_cast; rw [h0, h1]; ring
  have c11 : ((τ 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod N)) hτdet
    push_cast at this
    rw [c00, c10] at this
    linear_combination this

  set W : SL(2, ℤ) := τ * ModularGroup.T ^ (-(τ 0 1)) with hW
  have hWmem : W ∈ Gamma N := by
    have hmul : ∀ i j, (τ * ModularGroup.T ^ (-(τ 0 1)) : SL(2, ℤ)) i j =
        τ i 0 * (ModularGroup.T ^ (-(τ 0 1))) 0 j + τ i 1 * (ModularGroup.T ^ (-(τ 0 1))) 1 j := by
      intro i j
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Gamma_mem, hW, hmul, hmul, hmul, hmul, ModularGroup.coe_T_zpow]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero]
    push_cast
    refine ⟨c00, ?_, c10, ?_⟩
    · rw [c00]; ring
    · rw [c10, c11]; ring
  refine ⟨σ₂ * W * σ₂⁻¹, (Gamma_normal N).conj_mem W hWmem σ₂, fun m => ?_⟩
  have hσ₁ : σ₁ = σ₂ * τ := by rw [hτ]; group
  rw [hσ₁, hW]
  group

theorem Gamma_le_GammaH (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : Gamma N ≤ GammaH N H := by
  intro A hA
  rw [Gamma_mem] at hA
  obtain ⟨_, _, h10, h11⟩ := hA
  have h0 : A ∈ Gamma0 N := by rw [Gamma0_mem]; exact h10
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have : gamma0Units N ⟨A, h0⟩ = 1 := by
    apply Units.ext
    simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]; exact one_mem H

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

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ} {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A]

theorem mem_GammaHUpper_iff {r : ↥(GammaH N H)} :
    r ∈ GammaHUpper N H ℓ ↔ (ℓ : ℤ) ∣ (r : SL(2, ℤ)) 0 1 := by
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

def pOf (δ : SL(2, ℤ)) (r : ↥(GammaH N H)) : ℤ := ((r : SL(2, ℤ))⁻¹ * δ) 0 0

def qOf (δ : SL(2, ℤ)) (r : ↥(GammaH N H)) : ℤ := ((r : SL(2, ℤ))⁻¹ * δ) 1 0

theorem pOf_eq (δ : SL(2, ℤ)) (r : ↥(GammaH N H)) :
    pOf δ r = (r : SL(2, ℤ)) 1 1 * δ 0 0 - (r : SL(2, ℤ)) 0 1 * δ 1 0 := by
  unfold pOf
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable (δ : SL(2, ℤ)) (h : ℤ) (ε : SL(2, ℤ)) (hε : ε = 1 ∨ ε = -1) (u : ↥(GammaH N H))
  (hu : (u : SL(2, ℤ)) = ε * unipMat (δ 0 0) (δ 1 0) h)

include hε hu in

private theorem _root_.CohCarrier.BoundaryEisH.coe_pow (n : ℕ) : ((u ^ n : ↥(GammaH N H)) : SL(2, ℤ)) = ε ^ n * unipMat (δ 0 0) (δ 1 0) (h * n) := by
  rw [Subgroup.coe_pow, hu, Commute.mul_pow (sign_comm hε _) n, unipMat_pow]

p2m_export "CohCarrier.BoundaryEisH" "coe_pow"
include hε hu in

theorem coe_inv_mul_pow_mul (r : ↥(GammaH N H)) (n : ℕ) :
    ((r⁻¹ * u ^ n * r : ↥(GammaH N H)) : SL(2, ℤ)) = ε ^ n * unipMat (pOf δ r) (qOf δ r) (h * n) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_pow δ h ε hε u hu,
    sign_conj_inv (sign_pow_eq_or hε n), inv_mul_unipMat_mul]
  rfl

include hε hu in
theorem inv_mul_pow_mul_mem_iff (r : ↥(GammaH N H)) (n : ℕ) :
    r⁻¹ * u ^ n * r ∈ GammaHUpper N H ℓ ↔ (ℓ : ℤ) ∣ h * n * pOf δ r * pOf δ r := by
  rw [mem_GammaHUpper_iff, coe_inv_mul_pow_mul δ h ε hε u hu, dvd_sign_mul_apply_01_iff (sign_pow_eq_or hε n),
    unipMat_apply_01]

include hε hu in
theorem pow_smul_coe_eq_iff (r : ↥(GammaH N H)) (n : ℕ) :
    u ^ n • ((r : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) = r ↔
      (ℓ : ℤ) ∣ h * n * pOf δ r * pOf δ r := by
  rw [← inv_mul_pow_mul_mem_iff δ h ε hε u hu, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
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
theorem dvd_pOf_iff (r : ↥(GammaH N H)) : (ℓ : ℤ) ∣ pOf δ r ↔ r ∈ GammaHUpper N H ℓ := by
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

include hε hu hℓ hδ in
theorem minimalPeriod_eq_m₀ (r : ↥(GammaH N H)) (hr : r ∉ GammaHUpper N H ℓ) :
    Function.minimalPeriod (u • ·) ((r : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) = m₀ ℓ h := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  unfold m₀
  split_ifs with hh
  · rw [Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt]
    have := (pow_smul_coe_eq_iff (ℓ := ℓ) δ h ε hε u hu r 1).mpr (by
      simpa using dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hh _) _)
    simpa using this
  · haveI : Fact ℓ.Prime := ⟨hℓ⟩
    apply Function.minimalPeriod_eq_prime
    · rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
      exact (pow_smul_coe_eq_iff (ℓ := ℓ) δ h ε hε u hu r ℓ).mpr
        (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
    · rw [Function.IsFixedPt]
      intro hfix
      have := (pow_smul_coe_eq_iff (ℓ := ℓ) δ h ε hε u hu r 1).mp (by simpa using hfix)
      simp only [Nat.cast_one, mul_one] at this
      rcases hprime.dvd_or_dvd this with h1 | h1
      · rcases hprime.dvd_or_dvd h1 with h2 | h2
        · exact hh h2
        · exact hp h2
      · exact hp h1

abbrev OrbQ (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (u : ↥(GammaH N H)) : Type :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers u) (↥(GammaH N H) ⧸ GammaHUpper N H ℓ))

def orbOne (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (u : ↥(GammaH N H)) : OrbQ N H ℓ u :=
  Quotient.mk _ (((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ))

theorem orbOne_out (huK : u ∈ GammaHUpper N H ℓ) :
    (orbOne N H ℓ u).out = (((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) := by
  have hrel : (orbOne N H ℓ u).out ∈ MulAction.orbit (Subgroup.zpowers u)
      (((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) :=
    MulAction.orbitRel_apply.mp (Quotient.mk_out _)
  obtain ⟨z, hz⟩ := MulAction.mem_orbit_iff.mp hrel
  rw [← hz]
  change ((((z : ↥(GammaH N H)) * 1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) = _
  rw [mul_one, QuotientGroup.eq, mul_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
  rw [← hk]
  exact inv_mem (Subgroup.zpow_mem _ huK k)

theorem orbOne_out_out_mem (huK : u ∈ GammaHUpper N H ℓ) :
    (orbOne N H ℓ u).out.out ∈ GammaHUpper N H ℓ := by
  have h1 : (((orbOne N H ℓ u).out.out : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) =
      ((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) := by
    rw [QuotientGroup.out_eq', orbOne_out u huK]
  have := QuotientGroup.eq.mp h1.symm
  rwa [inv_one, one_mul] at this

theorem eq_orbOne_of_mem (O : OrbQ N H ℓ u) (hO : O.out.out ∈ GammaHUpper N H ℓ) : O = orbOne N H ℓ u := by
  have h1 : O.out = ((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) := by
    rw [← QuotientGroup.out_eq' O.out]
    symm
    exact QuotientGroup.eq.mpr (by rwa [inv_one, one_mul])
  rw [← Quotient.out_eq O, h1]
  rfl

theorem minimalPeriod_orbOne_out (huK : u ∈ GammaHUpper N H ℓ) :
    Function.minimalPeriod (u • ·) (orbOne N H ℓ u).out = 1 := by
  rw [orbOne_out u huK, Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt,
    MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
  exact inv_mem huK

variable (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N])

include hℓ1 in
theorem ell_cast_eq_one : ((ℓ : ℕ) : ZMod N) = 1 := by
  have := (ZMod.natCast_eq_natCast_iff ℓ 1 N).mpr hℓ1
  rwa [Nat.cast_one] at this

theorem conjUpperMat_congr {X Y : SL(2, ℤ)} (hXY : X = Y) (hX : (ℓ : ℤ) ∣ X 0 1) (hY : (ℓ : ℤ) ∣ Y 0 1) :
    conjUpperMat ℓ X hX = conjUpperMat ℓ Y hY := by
  subst hXY; rfl

theorem coe_conjL (x : ↥(GammaHUpper N H ℓ)) :
    ((conjL N H ℓ x : ↥(GammaH N H)) : SL(2, ℤ)) =
      conjUpperMat ℓ ((x : ↥(GammaH N H)) : SL(2, ℤ)) (dvd_of_mem_GammaHUpper N H ℓ x) := rfl

include hε hu hδ in
theorem u_mem_upper : u ∈ GammaHUpper N H ℓ := by
  rw [mem_GammaHUpper_iff, hu, dvd_sign_mul_apply_01_iff hε, unipMat_apply_01]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _

include hε hu in
theorem N_dvd : (N : ℤ) ∣ h * δ 1 0 * δ 1 0 := by
  have := (mem_GammaH_iff.mp u.2).1
  rw [hu, Gamma0_mem] at this
  rcases hε with rfl | rfl
  · rw [one_mul] at this
    exact (unipMat_mem_Gamma0_iff N _ _ _).mp (Gamma0_mem.mpr this)
  · rw [neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero] at this
    exact (unipMat_mem_Gamma0_iff N _ _ _).mp (Gamma0_mem.mpr this)

variable (hεℓ : ε ^ (ℓ + 1) = 1)

include hu hε hℓ hδ hℓ1 hεℓ in

theorem termOf_u (φ : H1 N H A) :
    termOf N H ℓ φ u (u_mem_upper δ h ε hε u hu hδ) = ℓ • φ (Additive.ofMul u) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hae : IsCoprime (δ 0 0) (δ 1 0) := isCoprime_col δ
  have ha'e : IsCoprime (δ 0 0 / ℓ) (δ 1 0) := by
    obtain ⟨a', ha'⟩ := hδ
    rw [ha', Int.mul_ediv_cancel_left _ hℓ0]
    rw [ha'] at hae
    exact hae.of_mul_left_right
  obtain ⟨σ₂, hσ00, hσ10⟩ := exists_SL2_col ha'e

  have hdvd : (ℓ : ℤ) ∣ (unipMat (δ 0 0) (δ 1 0) h) 0 1 := by
    rw [unipMat_apply_01]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _
  have hval : ((conjL N H ℓ ⟨u, u_mem_upper δ h ε hε u hu hδ⟩ : ↥(GammaH N H)) : SL(2, ℤ)) =
      ε * (σ₂ * ModularGroup.T ^ (h * ℓ) * σ₂⁻¹) := by
    rw [coe_conjL, conj_T_zpow_eq_unipMat, hσ00, hσ10]
    rw [conjUpperMat_congr hu (dvd_of_mem_GammaHUpper N H ℓ ⟨u, u_mem_upper δ h ε hε u hu hδ⟩)
      ((dvd_sign_mul_apply_01_iff hε _ _).mpr hdvd), conjUpperMat_sign_mul ℓ hε _ _ hdvd]
    rw [conjUpperMat_unipMat_of_dvd_left ℓ hℓ0 hδ _ _ _]

  have hc0 : ((δ 0 0 : ℤ) : ZMod N) = σ₂ 0 0 := by
    rw [hσ00]
    obtain ⟨a', ha'⟩ := hδ
    rw [ha', Int.mul_ediv_cancel_left _ hℓ0]
    push_cast
    rw [ell_cast_eq_one hℓ1, one_mul]
  have hc1 : ((δ 1 0 : ℤ) : ZMod N) = σ₂ 1 0 := by rw [hσ10]
  obtain ⟨g, hg, hconj⟩ := exists_conj_of_col_congr N δ σ₂ hc0 hc1
  set g' : ↥(GammaH N H) := ⟨g, Gamma_le_GammaH N H hg⟩ with hg'
  have hpow : ((u ^ ℓ : ↥(GammaH N H)) : SL(2, ℤ)) = ε ^ ℓ * (δ * ModularGroup.T ^ (h * ℓ) * δ⁻¹) := by
    rw [coe_pow δ h ε hε u hu, conj_T_zpow_eq_unipMat]
  have hεε : ε ^ ℓ = ε := sign_pow_succ_eq_one_iff hε ℓ hεℓ
  have hkey : conjL N H ℓ ⟨u, u_mem_upper δ h ε hε u hu hδ⟩ = g'⁻¹ * u ^ ℓ * g' := by
    apply Subtype.ext
    rw [hval, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hpow, hconj (h * ℓ), hεε, hg',
      Subgroup.coe_mk, sign_conj_inv hε]
    congr 1
    group
  unfold termOf
  rw [hkey, apply_inv_conj, ofMul_pow, map_nsmul]

def m₁ (ℓ : ℕ) (h : ℤ) : ℤ := h * (m₀ ℓ h : ℕ) / ℓ

include hℓ in
theorem m₁_mul : m₁ ℓ h * ℓ = h * (m₀ ℓ h : ℕ) := by
  unfold m₁
  exact Int.ediv_mul_cancel (dvd_h_mul_m₀ h)

include hu hε hℓ hδ hℓN hℓ1 hεℓ in

theorem uStar_mem : ε ^ (m₀ ℓ h) * unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h) ∈ GammaH N H := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hεε : ε ^ ℓ = ε := sign_pow_succ_eq_one_iff hε ℓ hεℓ
  by_cases hh : (ℓ : ℤ) ∣ h
  ·
    have hm₀ : m₀ ℓ h = 1 := by simp [m₀, hh]
    obtain ⟨h', hh'⟩ := hh
    have hm₁ : m₁ ℓ h = h' := by
      rw [m₁, hm₀, Nat.cast_one, mul_one, hh', Int.mul_ediv_cancel_left _ hℓ0]
    rw [hm₀, hm₁, pow_one]
    obtain ⟨hu0, huH⟩ := mem_GammaH_iff.mp u.2

    have hN := N_dvd δ h ε hε u hu
    rw [hh'] at hN
    have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
    have hN' : (N : ℤ) ∣ h' * δ 1 0 * δ 1 0 := by
      refine hcop.dvd_of_dvd_mul_left ?_
      rw [show (ℓ : ℤ) * (h' * δ 1 0 * δ 1 0) = (ℓ : ℤ) * h' * δ 1 0 * δ 1 0 by ring]
      exact hN
    have hmem0 : unipMat (δ 0 0) (δ 1 0) h' ∈ Gamma0 N := (unipMat_mem_Gamma0_iff N _ _ _).mpr hN'
    have h0 : ε * unipMat (δ 0 0) (δ 1 0) h' ∈ Gamma0 N := by
      rcases hε with rfl | rfl
      · rw [one_mul]; exact hmem0
      · rw [Gamma0_mem, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg,
          neg_eq_zero]
        exact Gamma0_mem.mp hmem0
    refine mem_GammaH_iff.mpr ⟨h0, ?_⟩

    obtain ⟨a', ha'⟩ := hδ
    have hunit : gamma0Units N ⟨_, h0⟩ = gamma0Units N ⟨(u : SL(2, ℤ)), hu0⟩ := by
      apply Units.ext
      show ((((ε * unipMat (δ 0 0) (δ 1 0) h') 1 1 : ℤ)) : ZMod N) = ((((u : SL(2, ℤ)) 1 1 : ℤ)) : ZMod N)
      rw [hu, hh']
      rcases hε with rfl | rfl
      · rw [one_mul, one_mul, unipMat_apply_11, unipMat_apply_11, ha']
        push_cast
        simp only [ell_cast_eq_one hℓ1]; ring
      · rw [neg_one_mul, neg_one_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.neg_apply, Matrix.neg_apply, unipMat_apply_11, unipMat_apply_11, ha']
        push_cast
        simp only [ell_cast_eq_one hℓ1]; ring
    rw [hunit]
    convert huH
  ·
    have hm₀ : m₀ ℓ h = ℓ := by simp [m₀, hh]
    have hm₁ : m₁ ℓ h = h := by
      rw [m₁, hm₀, Int.mul_ediv_cancel _ hℓ0]
    rw [hm₀, hm₁, hεε, ← hu]
    exact u.2

def uStar : ↥(GammaH N H) :=
  ⟨ε ^ (m₀ ℓ h) * unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h), uStar_mem δ h ε hε u hu hℓ hδ hℓN hℓ1 hεℓ⟩

include hδ hℓ1 in

theorem termOf_other (φ : H1 N H A) (r : ↥(GammaH N H)) (hr : r ∉ GammaHUpper N H ℓ)
    (hmem : r⁻¹ * u ^ (m₀ ℓ h) * r ∈ GammaHUpper N H ℓ) :
    termOf N H ℓ φ (r⁻¹ * u ^ (m₀ ℓ h) * r) hmem =
      φ (Additive.ofMul (uStar δ h ε hε u hu hℓ hδ hℓN hℓ1 hεℓ)) := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  have hpq : IsCoprime (pOf δ r) (qOf δ r) := isCoprime_col _
  have hpℓq : IsCoprime (pOf δ r) ((ℓ : ℤ) * qOf δ r) :=
    IsCoprime.mul_right ((Prime.coprime_iff_not_dvd hprime).mpr hp).symm hpq
  obtain ⟨σ₁, hσ00, hσ10⟩ := exists_SL2_col hpℓq
  have hdvd : (ℓ : ℤ) ∣ (unipMat (pOf δ r) (qOf δ r) (h * (m₀ ℓ h : ℕ))) 0 1 := by
    rw [unipMat_apply_01]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_h_mul_m₀ h) _) _
  have hval : ((conjL N H ℓ ⟨_, hmem⟩ : ↥(GammaH N H)) : SL(2, ℤ)) =
      ε ^ (m₀ ℓ h) * (σ₁ * ModularGroup.T ^ (m₁ ℓ h) * σ₁⁻¹) := by
    rw [coe_conjL, conj_T_zpow_eq_unipMat, hσ00, hσ10]
    rw [conjUpperMat_congr (coe_inv_mul_pow_mul δ h ε hε u hu r (m₀ ℓ h))
      (dvd_of_mem_GammaHUpper N H ℓ ⟨_, hmem⟩)
      ((dvd_sign_mul_apply_01_iff (sign_pow_eq_or hε _) _ _).mpr hdvd),
      conjUpperMat_sign_mul ℓ (sign_pow_eq_or hε _) _ _ hdvd]
    rw [conjUpperMat_unipMat_of_dvd_exp ℓ hℓ0 _ _ (dvd_h_mul_m₀ h) _]
    rfl

  have hc0 : ((σ₁ 0 0 : ℤ) : ZMod N) = ((r : SL(2, ℤ))⁻¹ * δ) 0 0 := by rw [hσ00]; rfl
  have hc1 : ((σ₁ 1 0 : ℤ) : ZMod N) = ((r : SL(2, ℤ))⁻¹ * δ) 1 0 := by
    rw [hσ10]; push_cast; rw [ell_cast_eq_one hℓ1, one_mul]; rfl
  obtain ⟨g, hg, hconj⟩ := exists_conj_of_col_congr N σ₁ ((r : SL(2, ℤ))⁻¹ * δ) hc0 hc1
  set g' : ↥(GammaH N H) := ⟨g, Gamma_le_GammaH N H hg⟩ with hg'
  have hkey : conjL N H ℓ ⟨_, hmem⟩ =
      (g' * r⁻¹) * uStar δ h ε hε u hu hℓ hδ hℓN hℓ1 hεℓ * (g' * r⁻¹)⁻¹ := by
    apply Subtype.ext
    rw [hval, hconj (m₁ ℓ h)]
    show ε ^ m₀ ℓ h * (g * ((r : SL(2, ℤ))⁻¹ * δ * ModularGroup.T ^ m₁ ℓ h * ((r : SL(2, ℤ))⁻¹ * δ)⁻¹) * g⁻¹) =
      g * (r : SL(2, ℤ))⁻¹ * (ε ^ (m₀ ℓ h) * unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h)) * (g * (r : SL(2, ℤ))⁻¹)⁻¹
    rw [← conj_T_zpow_eq_unipMat, sign_conj_left (sign_pow_eq_or hε _)]
    congr 1
    group
  unfold termOf
  rw [hkey, apply_conj]

include hu hε hℓ hδ hℓN hℓ1 hεℓ in

theorem heckeT_apply_u (φ : H1 N H A) :
    heckeT N H ℓ A φ (Additive.ofMul u) = (ℓ + 1) • φ (Additive.ofMul u) := by
  classical
  haveI : Fintype (OrbQ N H ℓ u) := Fintype.ofFinite _
  have huK := u_mem_upper δ h ε hε u hu hδ
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hper : ∀ O : OrbQ N H ℓ u, O ≠ orbOne N H ℓ u →
      Function.minimalPeriod (u • ·) O.out = m₀ ℓ h := by
    intro O hO
    have hr : O.out.out ∉ GammaHUpper N H ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have := minimalPeriod_eq_m₀ δ h ε hε u hu hℓ hδ O.out.out hr
    rwa [QuotientGroup.out_eq'] at this
  have hterm : ∀ O : OrbQ N H ℓ u, O ≠ orbOne N H ℓ u →
      termOf N H ℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
        (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out) =
      φ (Additive.ofMul (uStar δ h ε hε u hu hℓ hδ hℓN hℓ1 hεℓ)) := by
    intro O hO
    have hr : O.out.out ∉ GammaHUpper N H ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have hmem : O.out.out⁻¹ * u ^ (m₀ ℓ h) * O.out.out ∈ GammaHUpper N H ℓ := by
      have := QuotientGroup.out_conj_pow_minimalPeriod_mem (GammaHUpper N H ℓ) u O.out
      rwa [hper O hO] at this
    rw [termOf_congr N H ℓ φ _ hmem (by rw [hper O hO])]
    exact termOf_other δ h ε hε u hu hℓ hδ hℓN hℓ1 hεℓ φ O.out.out hr hmem
  have hone : termOf N H ℓ φ ((orbOne N H ℓ u).out.out⁻¹ *
      u ^ Function.minimalPeriod (u • ·) (orbOne N H ℓ u).out * (orbOne N H ℓ u).out.out)
      (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u _) = ℓ • φ (Additive.ofMul u) := by
    have hr := orbOne_out_out_mem u huK
    have hmem : (orbOne N H ℓ u).out.out⁻¹ * u * (orbOne N H ℓ u).out.out ∈ GammaHUpper N H ℓ :=
      mul_mem (mul_mem (inv_mem hr) huK) hr
    rw [termOf_congr N H ℓ φ _ hmem (by rw [minimalPeriod_orbOne_out u huK, pow_one]),
      termOf_conj N H ℓ φ huK hr hmem]
    exact termOf_u δ h ε hε u hu hℓ hδ hℓ1 hεℓ φ
  have hidx : ℓ + 1 = ∑ O : OrbQ N H ℓ u, Function.minimalPeriod (u • ·) O.out := by
    rw [← CohCarrier.index_GammaHUpper_of_prime N H ℓ hℓ hℓN]
    exact Subgroup.index_eq_sum_minimalPeriod _ u
  rw [Finset.sum_eq_add_sum_sdiff_singleton (orbOne N H ℓ u) _ (fun h => (h (Finset.mem_univ _)).elim),
    minimalPeriod_orbOne_out u huK, Finset.sum_congr rfl (fun O hO => hper O (by simpa using hO)),
    Finset.sum_const, smul_eq_mul, add_comm, Nat.add_left_cancel_iff] at hidx
  rw [heckeT_apply_eq_sum_orbits,
    Finset.sum_eq_add_sum_sdiff_singleton (orbOne N H ℓ u) _ (fun h => (h (Finset.mem_univ _)).elim),
    hone, Finset.sum_congr rfl (fun O hO => hterm O (by simpa using hO)), Finset.sum_const, succ_nsmul]
  congr 1
  have hεε : ε ^ ℓ = ε := sign_pow_succ_eq_one_iff hε ℓ hεℓ
  by_cases hh : (ℓ : ℤ) ∣ h
  · have hm₀ : m₀ ℓ h = 1 := by simp [m₀, hh]
    rw [hm₀, mul_one] at hidx
    rw [← hidx, ← map_nsmul, ← ofMul_pow]
    congr 2
    apply Subtype.ext
    rw [Subgroup.coe_pow, hu]
    show (ε ^ (m₀ ℓ h) * unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h)) ^ ℓ = ε * unipMat (δ 0 0) (δ 1 0) h
    rw [hm₀, pow_one, Commute.mul_pow (sign_comm hε _) ℓ, hεε, unipMat_pow, m₁_mul h hℓ, hm₀,
      Nat.cast_one, mul_one]
  · have hm₀ : m₀ ℓ h = ℓ := by simp [m₀, hh]
    rw [hm₀, eq_comm, mul_eq_right₀ hℓ.ne_zero] at hidx
    rw [hidx, one_smul]
    congr 2
    apply Subtype.ext
    rw [hu]
    show ε ^ (m₀ ℓ h) * unipMat (δ 0 0) (δ 1 0) (m₁ ℓ h) = ε * unipMat (δ 0 0) (δ 1 0) h
    have hm₁ : m₁ ℓ h = h := by rw [m₁, hm₀, Int.mul_ediv_cancel _ hℓ0]
    rw [hm₁, hm₀, hεε]

end Main

section Assembly

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ} {ℓ : ℕ} [NeZero ℓ] {A : Type*} [AddCommGroup A]
  (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N])

include hℓ hℓN hℓ1 in

theorem exists_mul_dvd (δ : SL(2, ℤ)) : ∃ g ∈ GammaH N H, (ℓ : ℤ) ∣ (g * δ) 0 0 := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  by_cases he : (ℓ : ℤ) ∣ δ 1 0
  ·
    obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)
    set g₀ : SL(2, ℤ) := ⟨!![(ℓ : ℤ), -y; (N : ℤ), x], by rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
      with hg₀
    have h0 : g₀ ∈ Gamma0 N := by rw [Gamma0_mem, hg₀]; simp
    refine ⟨g₀, mem_GammaH_iff.mpr ⟨h0, ?_⟩, ?_⟩
    · have hx : ((x : ℤ) : ZMod N) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod N)) hxy
        push_cast at this
        rw [ell_cast_eq_one hℓ1, ZMod.natCast_self] at this
        linear_combination this
      have : gamma0Units N ⟨g₀, h0⟩ = 1 := by
        apply Units.ext
        show (((g₀ 1 1 : ℤ)) : ZMod N) = 1
        rw [hg₀]
        simpa using hx
      rw [this]; exact one_mem H
    · rw [hg₀, Matrix.SpecialLinearGroup.coe_mul]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right he _)
  · obtain ⟨x, z, hxz⟩ := (Prime.coprime_iff_not_dvd hprime).mpr he
    refine ⟨ModularGroup.T ^ (-(δ 0 0 * z)), ?_, ?_⟩
    · have : ModularGroup.T ^ (-(δ 0 0 * z)) = uMat (-(δ 0 0 * z)) := by
        apply Matrix.SpecialLinearGroup.ext; intro i j
        rw [ModularGroup.coe_T_zpow]
        fin_cases i <;> fin_cases j <;> rfl
      rw [this]; exact uMat_mem_GammaH N H _
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
    exact ⟨δ 0 0 * x, by linear_combination (-(δ 0 0)) * hxz⟩

include hℓ hℓN hℓ1 in

theorem heckeT_apply_signed_parabolic (φ : H1 N H A) (δ : SL(2, ℤ)) (h : ℤ) (ε : SL(2, ℤ))
    (hε : ε = 1 ∨ ε = -1) (hεℓ : ε ^ (ℓ + 1) = 1) (u : ↥(GammaH N H))
    (hu : (u : SL(2, ℤ)) = ε * (δ * ModularGroup.T ^ h * δ⁻¹)) :
    heckeT N H ℓ A φ (Additive.ofMul u) = (ℓ + 1) • φ (Additive.ofMul u) := by
  obtain ⟨g, hg, hdvd⟩ := exists_mul_dvd hℓ hℓN hℓ1 δ
  set g' : ↥(GammaH N H) := ⟨g, hg⟩ with hg'
  set u' : ↥(GammaH N H) := g' * u * g'⁻¹ with hu'def
  have hu' : (u' : SL(2, ℤ)) = ε * unipMat ((g * δ) 0 0) ((g * δ) 1 0) h := by
    rw [hu'def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu, hg', ← conj_T_zpow_eq_unipMat]
    show g * (ε * (δ * ModularGroup.T ^ h * δ⁻¹)) * g⁻¹ = ε * (g * δ * ModularGroup.T ^ h * (g * δ)⁻¹)
    rw [← mul_assoc g ε, ← sign_comm hε g]
    group
  have key := heckeT_apply_u (g * δ) h ε hε u' hu' hℓ hdvd hℓN hℓ1 hεℓ φ
  rwa [hu'def, apply_conj, apply_conj] at key

theorem conjUpperMat_neg_one (hn : (ℓ : ℤ) ∣ (-1 : SL(2, ℤ)) 0 1) : conjUpperMat ℓ (-1) hn = -1 := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [conjUpperMat, Matrix.SpecialLinearGroup.coe_neg]

theorem conjUpperMat_congr' {X Y : SL(2, ℤ)} (hXY : X = Y) (hX : (ℓ : ℤ) ∣ X 0 1) (hY : (ℓ : ℤ) ∣ Y 0 1) :
    conjUpperMat ℓ X hX = conjUpperMat ℓ Y hY := by
  subst hXY; rfl

include hℓ hℓN in

theorem heckeT_apply_neg_one (φ : H1 N H A) (ε : ↥(GammaH N H)) (hε : (ε : SL(2, ℤ)) = -1) :
    heckeT N H ℓ A φ (Additive.ofMul ε) = (ℓ + 1) • φ (Additive.ofMul ε) := by
  have hcomm : ∀ x : ↥(GammaH N H), Commute ε x := fun x => by
    show ε * x = x * ε
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hε, neg_one_mul, mul_neg_one]
  have key : ∀ (k : ℕ) (g₀ : ↥(GammaH N H)), g₀⁻¹ * ε ^ k * g₀ ∈ GammaHUpper N H ℓ →
      g₀⁻¹ * ε ^ k * g₀ = ε ^ k := fun k g₀ _ => by
    rw [mul_assoc, ((hcomm g₀).pow_left k).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hεK : ε ∈ GammaHUpper N H ℓ := by
    rw [mem_GammaHUpper_iff, hε, Matrix.SpecialLinearGroup.coe_neg]
    simp
  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL N H ℓ)) ε) = _
  rw [MonoidHom.transfer_eq_pow _ ε key]
  have hpow : (⟨ε ^ (GammaHUpper N H ℓ).index, MonoidHom.transfer_eq_pow_aux ε key⟩ :
      ↥(GammaHUpper N H ℓ)) = ⟨ε, hεK⟩ ^ (ℓ + 1) := by
    apply Subtype.ext
    simp [CohCarrier.index_GammaHUpper_of_prime N H ℓ hℓ hℓN]
  have hfix : conjL N H ℓ ⟨ε, hεK⟩ = ε := by
    apply Subtype.ext
    rw [coe_conjL]
    show conjUpperMat ℓ (ε : SL(2, ℤ)) _ = _
    rw [conjUpperMat_congr' hε _ (by rw [Matrix.SpecialLinearGroup.coe_neg]; simp), conjUpperMat_neg_one, hε]
  rw [hpow, map_pow, MonoidHom.comp_apply, hfix, toAdd_pow]
  rfl

theorem neg_one_pow_succ_of_not_mem (hℓ : ℓ.Prime) (hℓ1 : ℓ ≡ 1 [MOD N])
    (hneg : (-1 : SL(2, ℤ)) ∉ GammaH N H) : (-1 : SL(2, ℤ)) ^ (ℓ + 1) = 1 := by
  rcases hℓ.eq_two_or_odd' with rfl | hodd
  ·
    exfalso
    have hN : N ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num)).mp hℓ1.symm
    have hN1 : N = 1 := Nat.dvd_one.mp hN
    subst hN1
    apply hneg
    have h0 : (-1 : SL(2, ℤ)) ∈ Gamma0 1 := by
      rw [Gamma0_mem]; exact Subsingleton.elim _ _
    exact mem_GammaH_iff.mpr ⟨h0, by
      have : gamma0Units 1 ⟨-1, h0⟩ = 1 := Subsingleton.elim _ _
      rw [this]; exact one_mem H⟩
  · exact (hodd.add_odd odd_one).neg_one_pow

include hℓ hℓN hℓ1 in

theorem heckeT_apply_of_trace_sq (φ : H1 N H A) (γ : ↥(GammaH N H))
    (hγ : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace) ^ 2 = 4) :
    heckeT N H ℓ A φ (Additive.ofMul γ) = (ℓ + 1) • φ (Additive.ofMul γ) := by
  obtain ⟨ε, δ, h, hε, hγeq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
  by_cases hmem : ε ∈ GammaH N H
  ·
    set ε' : ↥(GammaH N H) := ⟨ε, hmem⟩ with hε'
    set u : ↥(GammaH N H) := ε'⁻¹ * γ with hudef
    have hu : (u : SL(2, ℤ)) = 1 * (δ * ModularGroup.T ^ h * δ⁻¹) := by
      rw [hudef, Subgroup.coe_mul, Subgroup.coe_inv, hγeq, hε', one_mul]
      group
    have hγu : γ = ε' * u := by rw [hudef]; group
    have hεT : heckeT N H ℓ A φ (Additive.ofMul ε') = (ℓ + 1) • φ (Additive.ofMul ε') := by
      rcases hε with h1 | h1
      · have : ε' = 1 := Subtype.ext h1
        rw [this, ofMul_one, map_zero, map_zero, smul_zero]
      · exact heckeT_apply_neg_one hℓ hℓN φ ε' h1
    rw [hγu, ofMul_mul, map_add, map_add, hεT,
      heckeT_apply_signed_parabolic hℓ hℓN hℓ1 φ δ h 1 (Or.inl rfl) (one_pow _) u hu, smul_add]
  ·
    have hε1 : ε = -1 := by
      rcases hε with rfl | rfl
      · exact absurd (one_mem _) hmem
      · rfl
    subst hε1
    exact heckeT_apply_signed_parabolic hℓ hℓN hℓ1 φ δ h (-1) (Or.inr rfl)
      (neg_one_pow_succ_of_not_mem hℓ hℓ1 hmem) γ hγeq

end Assembly

end CohCarrier.BoundaryEisH
p2m_reactivate "P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.CohCarrier P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.CohCarrier.BoundaryEisH"
p2m_reactivate "P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.CohCarrier"

open CohCarrier.BoundaryEisH in
theorem solution
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N H A) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N]) :
    CohCarrier.heckeT N H ℓ A φ - (ℓ + 1) • φ ∈
      ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) A := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff]
  intro γ hγ
  rw [AddMonoidHom.sub_apply, AddMonoidHom.nsmul_apply, sub_eq_zero]
  exact heckeT_apply_of_trace_sq hℓ hℓN hℓ1 φ γ hγ

end S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
end P2MW
export P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one (solution)
