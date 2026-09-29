-- Prove2me | solution 1 for CohCarrier.exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/e3cac934-e63f-510f-a8f4-c1586d31add8

import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_ModularCurve_PeriodMap
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_Module_End_exists_common_eigenvector_of_commute
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

namespace CohCarrier
p2m_export "CohCarrier" "gamma0Units_surjective diamondL mem_Gamma0Upper gamma0Units GammaH mem_GammaH_iff GammaH_le_Gamma0 H1 conjUpperMat conjUpperMat_apply_11 conjUpperMat_apply_10 GammaHUpper dvd_of_mem_GammaHUpper conjL heckeT conjHom uMat uMat_apply_00 uMat_apply_01 uMat_apply_10 uMat_apply_11 uMat_mem_GammaH index_GammaHUpper_of_prime"
namespace BdryEis
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

theorem unipMat_mem_Gamma (N : ℕ) (p q : ℤ) : unipMat p q N ∈ Gamma N := by
  rw [Gamma_mem]
  simp only [unipMat_apply_00, unipMat_apply_01, unipMat_apply_10, unipMat_apply_11]
  push_cast
  simp

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

private theorem _root_.CohCarrier.BdryEis.exists_SL2_col {p q : ℤ} (h : IsCoprime p q) : ∃ σ : SL(2, ℤ), σ 0 0 = p ∧ σ 1 0 = q := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨!![p, -y; q, x], ?_⟩, rfl, rfl⟩
  rw [Matrix.det_fin_two_of]
  linear_combination hxy

p2m_export "CohCarrier.BdryEis" "exists_SL2_col"
theorem isCoprime_col (δ : SL(2, ℤ)) : IsCoprime (δ 0 0) (δ 1 0) := by
  have hdet : δ 0 0 * δ 1 1 - δ 0 1 * δ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe δ
    rwa [Matrix.det_fin_two] at h
  exact ⟨δ 1 1, -(δ 0 1), by linear_combination hdet⟩

theorem conjUpperMat_congr {ℓ : ℕ} {X Y : SL(2, ℤ)} (hXY : X = Y) (hX : (ℓ : ℤ) ∣ X 0 1)
    (hY : (ℓ : ℤ) ∣ Y 0 1) : conjUpperMat ℓ X hX = conjUpperMat ℓ Y hY := by
  subst hXY; rfl

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

section CuspValues

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ} {A : Type*} [AddCommGroup A]

variable (N H) in

def uOf (δ : SL(2, ℤ)) : ↥(GammaH N H) :=
  ⟨δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹, by
    rw [conj_T_zpow_eq_unipMat]
    exact Gamma_le_GammaH N H (unipMat_mem_Gamma N _ _)⟩

@[scoped simp] theorem coe_uOf (δ : SL(2, ℤ)) :
    ((uOf N H δ : ↥(GammaH N H)) : SL(2, ℤ)) = δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ := rfl

def B (φ : H1 N H A) (δ : SL(2, ℤ)) : A := φ (Additive.ofMul (uOf N H δ))

theorem B_add (φ ψ : H1 N H A) (δ : SL(2, ℤ)) : B (φ + ψ) δ = B φ δ + B ψ δ := rfl

theorem B_smul {R : Type*} [Semiring R] [Module R A] (c : R) (φ : H1 N H A) (δ : SL(2, ℤ)) :
    B (c • φ) δ = c • B φ δ := rfl

theorem B_mul_left (φ : H1 N H A) (γ : ↥(GammaH N H)) (δ : SL(2, ℤ)) :
    B φ ((γ : SL(2, ℤ)) * δ) = B φ δ := by
  have : uOf N H ((γ : SL(2, ℤ)) * δ) = γ * uOf N H δ * γ⁻¹ := by
    apply Subtype.ext
    simp only [coe_uOf, Subgroup.coe_mul, InvMemClass.coe_inv]
    group
  unfold B
  rw [this, apply_conj]

def colRed (N : ℕ) (δ : SL(2, ℤ)) : ZMod N × ZMod N := (((δ 0 0 : ℤ) : ZMod N), ((δ 1 0 : ℤ) : ZMod N))

@[scoped simp] theorem colRed_fst (δ : SL(2, ℤ)) : (colRed N δ).1 = ((δ 0 0 : ℤ) : ZMod N) := rfl
@[scoped simp] theorem colRed_snd (δ : SL(2, ℤ)) : (colRed N δ).2 = ((δ 1 0 : ℤ) : ZMod N) := rfl

theorem B_congr (φ : H1 N H A) {δ δ' : SL(2, ℤ)} (h : colRed N δ = colRed N δ') : B φ δ = B φ δ' := by
  obtain ⟨g, hg, hconj⟩ := exists_conj_of_col_congr N δ δ' (congrArg Prod.fst h) (congrArg Prod.snd h)
  set g' : ↥(GammaH N H) := ⟨g, Gamma_le_GammaH N H hg⟩ with hg'
  have : uOf N H δ = g' * uOf N H δ' * g'⁻¹ := by
    apply Subtype.ext
    simp only [coe_uOf, Subgroup.coe_mul, InvMemClass.coe_inv, hg']
    exact hconj N
  unfold B
  rw [this, apply_conj]

theorem colRed_mul_of_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (X : SL(2, ℤ)) :
    colRed N (γ * X) = (((γ 0 0 : ℤ) : ZMod N) * ((X 0 0 : ℤ) : ZMod N) +
        ((γ 0 1 : ℤ) : ZMod N) * ((X 1 0 : ℤ) : ZMod N),
      ((γ 1 1 : ℤ) : ZMod N) * ((X 1 0 : ℤ) : ZMod N)) := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  have hmul : ∀ i j, (γ * X : SL(2, ℤ)) i j = γ i 0 * X 0 j + γ i 1 * X 1 j := fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  unfold colRed
  rw [hmul, hmul]
  push_cast
  rw [hc, zero_mul, zero_add]

theorem exists_borel (h : (ZMod N)ˣ) (hh : h ∈ H) (t : ZMod N) :
    ∃ γ : ↥(GammaH N H), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = ((h⁻¹ : (ZMod N)ˣ) : ZMod N) ∧
      (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) = t ∧ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (h : ZMod N) := by
  obtain ⟨σ, hσ⟩ := gamma0Units_surjective N h
  have h11 : (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = (h : ZMod N) := by
    rw [← hσ]; rfl
  have h00 : (((σ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) = ((h⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    rw [← hσ]; rfl

  set k : ℤ := (((t - (((σ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N)) * ((h⁻¹ : (ZMod N)ˣ) : ZMod N)).val : ℤ)
    with hk
  have hkval : ((k : ℤ) : ZMod N) = (t - (((σ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N)) *
      ((h⁻¹ : (ZMod N)ˣ) : ZMod N) := by
    rw [hk, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hσH : (σ : SL(2, ℤ)) ∈ GammaH N H := mem_GammaH_iff.mpr ⟨σ.2, by
    have : (⟨(σ : SL(2, ℤ)), σ.2⟩ : Gamma0 N) = σ := rfl
    rw [this, hσ]; exact hh⟩
  refine ⟨⟨uMat k, uMat_mem_GammaH N H k⟩ * ⟨σ, hσH⟩, ?_, ?_, ?_⟩
  all_goals
    simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, uMat_apply_00, uMat_apply_01, uMat_apply_10,
      uMat_apply_11, one_mul, zero_mul, zero_add]
  · push_cast
    rw [h00, Gamma0_mem.mp σ.2, mul_zero, add_zero]
  · push_cast
    rw [hkval, h11, mul_assoc, Units.inv_mul, mul_one]
    ring
  · exact h11

theorem B_eq_of_borel (φ : H1 N H A) {σ σ' : SL(2, ℤ)} (h : (ZMod N)ˣ) (hh : h ∈ H) (t : ZMod N)
    (h0 : (colRed N σ').1 = ((h⁻¹ : (ZMod N)ˣ) : ZMod N) * (colRed N σ).1 + t * (colRed N σ).2)
    (h1 : (colRed N σ').2 = (h : ZMod N) * (colRed N σ).2) : B φ σ' = B φ σ := by
  obtain ⟨γ, hγ0, hγ1, hγ2⟩ := exists_borel h hh t
  have hγ00 : (γ : SL(2, ℤ)) ∈ Gamma0 N := GammaH_le_Gamma0 H γ.2
  have hcol : colRed N σ' = colRed N ((γ : SL(2, ℤ)) * σ) := by
    rw [colRed_mul_of_mem_Gamma0 hγ00, hγ0, hγ1, hγ2]
    exact Prod.ext h0 h1
  rw [B_congr φ hcol, B_mul_left]

theorem exists_Gamma_mul_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (δ : SL(2, ℤ)) :
    ∃ g ∈ Gamma N, (ℓ : ℤ) ∣ (g * δ) 0 0 := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hNℓ : ¬ (ℓ : ℤ) ∣ (N : ℤ) := fun h => hℓN (Int.natCast_dvd_natCast.mp h)

  have step : ∀ δ : SL(2, ℤ), ¬ (ℓ : ℤ) ∣ δ 1 0 → ∃ g ∈ Gamma N, (ℓ : ℤ) ∣ (g * δ) 0 0 := by
    intro δ hc
    have hcop : IsCoprime ((N : ℤ) * δ 1 0) (ℓ : ℤ) := by
      apply IsCoprime.mul_left
      · exact (Prime.coprime_iff_not_dvd hprime).mpr hNℓ |>.symm
      · exact (Prime.coprime_iff_not_dvd hprime).mpr hc |>.symm
    obtain ⟨x, y, hxy⟩ := hcop
    refine ⟨ModularGroup.T ^ ((N : ℤ) * (-(δ 0 0 * x))), ?_, ?_⟩
    · have := ModularGroup_T_pow_mem_Gamma (N : ℤ) ((N : ℤ) * (-(δ 0 0 * x))) (dvd_mul_right _ _)
      rwa [Int.natAbs_natCast] at this
    · rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
      exact ⟨δ 0 0 * y, by linear_combination (-(δ 0 0)) * hxy⟩
  by_cases hc : (ℓ : ℤ) ∣ δ 1 0
  ·
    have ha : ¬ (ℓ : ℤ) ∣ δ 0 0 := by
      intro ha
      obtain ⟨x, y, hxy⟩ := isCoprime_col δ
      have h1 : (ℓ : ℤ) ∣ 1 := by
        rw [← hxy]; exact dvd_add (dvd_mul_of_dvd_right ha _) (dvd_mul_of_dvd_right hc _)
      exact hprime.not_dvd_one h1
    set L : SL(2, ℤ) := ⟨!![1, 0; (N : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩ with hL
    have hLmem : L ∈ Gamma N := by
      rw [Gamma_mem, hL]; simp
    have hLδ10 : (L * δ) 1 0 = N * δ 0 0 + δ 1 0 := by
      rw [hL, Matrix.SpecialLinearGroup.coe_mul]
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hc' : ¬ (ℓ : ℤ) ∣ (L * δ) 1 0 := by
      rw [hLδ10]
      intro h
      have : (ℓ : ℤ) ∣ (N : ℤ) * δ 0 0 := by simpa using dvd_sub h hc
      rcases hprime.dvd_or_dvd this with h' | h'
      · exact hNℓ h'
      · exact ha h'
    obtain ⟨g, hg, hdvd⟩ := step (L * δ) hc'
    exact ⟨g * L, mul_mem hg hLmem, by rwa [mul_assoc]⟩
  · exact step δ hc

end CuspValues

section Hecke

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

theorem qOf_eq (δ : SL(2, ℤ)) (r : ↥(GammaH N H)) :
    qOf δ r = -(r : SL(2, ℤ)) 1 0 * δ 0 0 + (r : SL(2, ℤ)) 0 0 * δ 1 0 := by
  unfold qOf
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

variable (δ : SL(2, ℤ))

theorem coe_uOf_eq_unipMat :
    ((uOf N H δ : ↥(GammaH N H)) : SL(2, ℤ)) = unipMat (δ 0 0) (δ 1 0) N :=
  conj_T_zpow_eq_unipMat δ N

theorem coe_uOf_pow (n : ℕ) :
    ((uOf N H δ ^ n : ↥(GammaH N H)) : SL(2, ℤ)) = unipMat (δ 0 0) (δ 1 0) ((N : ℤ) * n) := by
  rw [Subgroup.coe_pow, coe_uOf_eq_unipMat, unipMat_pow]

theorem coe_inv_mul_pow_mul (r : ↥(GammaH N H)) (n : ℕ) :
    ((r⁻¹ * uOf N H δ ^ n * r : ↥(GammaH N H)) : SL(2, ℤ)) =
      unipMat (pOf δ r) (qOf δ r) ((N : ℤ) * n) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_uOf_pow, inv_mul_unipMat_mul]
  rfl

theorem inv_mul_pow_mul_mem_iff (r : ↥(GammaH N H)) (n : ℕ) :
    r⁻¹ * uOf N H δ ^ n * r ∈ GammaHUpper N H ℓ ↔ (ℓ : ℤ) ∣ (N : ℤ) * n * pOf δ r * pOf δ r := by
  rw [mem_GammaHUpper_iff, coe_inv_mul_pow_mul, unipMat_apply_01]

theorem pow_smul_coe_eq_iff (r : ↥(GammaH N H)) (n : ℕ) :
    uOf N H δ ^ n • ((r : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) = r ↔
      (ℓ : ℤ) ∣ (N : ℤ) * n * pOf δ r * pOf δ r := by
  rw [← inv_mul_pow_mul_mem_iff δ r n, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq,
    ← inv_mem_iff, _root_.mul_inv_rev, inv_inv]
  simp only [mul_assoc]

variable (hℓ : ℓ.Prime) (hδ : (ℓ : ℤ) ∣ δ 0 0) (hℓN : ¬ ℓ ∣ N)

include hℓ hδ in
theorem not_dvd_e : ¬ (ℓ : ℤ) ∣ δ 1 0 := by
  intro he
  have h1 : (ℓ : ℤ) ∣ 1 := by
    obtain ⟨x, y, hxy⟩ := isCoprime_col δ
    rw [← hxy]; exact dvd_add (dvd_mul_of_dvd_right hδ _) (dvd_mul_of_dvd_right he _)
  exact (Nat.prime_iff_prime_int.mp hℓ).not_dvd_one h1

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

include hℓ hδ hℓN in

theorem minimalPeriod_eq (r : ↥(GammaH N H)) (hr : r ∉ GammaHUpper N H ℓ) :
    Function.minimalPeriod (uOf N H δ • ·) ((r : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ)) = ℓ := by
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  have hNℓ : ¬ (ℓ : ℤ) ∣ (N : ℤ) := fun h => hℓN (Int.natCast_dvd_natCast.mp h)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  apply Function.minimalPeriod_eq_prime
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, smul_iterate]
    exact (pow_smul_coe_eq_iff (ℓ := ℓ) δ r ℓ).mpr
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
  · rw [Function.IsFixedPt]
    intro hfix
    have := (pow_smul_coe_eq_iff (ℓ := ℓ) δ r 1).mp (by simpa using hfix)
    simp only [Nat.cast_one, mul_one] at this
    rcases hprime.dvd_or_dvd this with h1 | h1
    · rcases hprime.dvd_or_dvd h1 with h2 | h2
      · exact hNℓ h2
      · exact hp h2
    · exact hp h1

abbrev OrbQ (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (u : ↥(GammaH N H)) : Type :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers u) (↥(GammaH N H) ⧸ GammaHUpper N H ℓ))

def orbOne (N : ℕ) (H : Subgroup (ZMod N)ˣ) (ℓ : ℕ) (u : ↥(GammaH N H)) : OrbQ N H ℓ u :=
  Quotient.mk _ (((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ))

theorem orbOne_out (u : ↥(GammaH N H)) (huK : u ∈ GammaHUpper N H ℓ) :
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

theorem orbOne_out_out_mem (u : ↥(GammaH N H)) (huK : u ∈ GammaHUpper N H ℓ) :
    (orbOne N H ℓ u).out.out ∈ GammaHUpper N H ℓ := by
  have h1 : (((orbOne N H ℓ u).out.out : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) =
      ((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) := by
    rw [QuotientGroup.out_eq', orbOne_out u huK]
  have := QuotientGroup.eq.mp h1.symm
  rwa [inv_one, one_mul] at this

theorem eq_orbOne_of_mem (u : ↥(GammaH N H)) (O : OrbQ N H ℓ u)
    (hO : O.out.out ∈ GammaHUpper N H ℓ) : O = orbOne N H ℓ u := by
  have h1 : O.out = ((1 : ↥(GammaH N H)) : ↥(GammaH N H) ⧸ GammaHUpper N H ℓ) := by
    rw [← QuotientGroup.out_eq' O.out]
    symm
    exact QuotientGroup.eq.mpr (by rwa [inv_one, one_mul])
  rw [← Quotient.out_eq O, h1]
  rfl

theorem minimalPeriod_orbOne_out (u : ↥(GammaH N H)) (huK : u ∈ GammaHUpper N H ℓ) :
    Function.minimalPeriod (u • ·) (orbOne N H ℓ u).out = 1 := by
  rw [orbOne_out u huK, Function.minimalPeriod_eq_one_iff_isFixedPt, Function.IsFixedPt,
    MulAction.Quotient.smul_coe, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
  exact inv_mem huK

include hδ in
theorem uOf_mem_upper : uOf N H δ ∈ GammaHUpper N H ℓ := by
  rw [mem_GammaHUpper_iff, coe_uOf_eq_unipMat, unipMat_apply_01]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hδ _) _

include hℓ hδ in

theorem termOf_u (φ : H1 N H A) :
    ∃ σ₂ : SL(2, ℤ), σ₂ 0 0 * ℓ = δ 0 0 ∧ σ₂ 1 0 = δ 1 0 ∧
      termOf N H ℓ φ (uOf N H δ) (uOf_mem_upper δ hδ) = ℓ • B φ σ₂ := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hae : IsCoprime (δ 0 0) (δ 1 0) := isCoprime_col δ
  obtain ⟨a', ha'⟩ := id hδ
  have ha'e : IsCoprime a' (δ 1 0) := by rw [ha'] at hae; exact hae.of_mul_left_right
  obtain ⟨σ₂, hσ00, hσ10⟩ := exists_SL2_col ha'e
  refine ⟨σ₂, by rw [hσ00, ha', mul_comm], hσ10, ?_⟩
  have hdvd : (ℓ : ℤ) ∣ (unipMat (δ 0 0) (δ 1 0) N) 0 1 := by
    rw [unipMat_apply_01, ha']; exact ⟨N * a' * (ℓ * a'), by ring⟩
  have hdiv : δ 0 0 / ℓ = a' := by rw [ha', Int.mul_ediv_cancel_left _ hℓ0]
  have hval : ((conjL N H ℓ ⟨uOf N H δ, uOf_mem_upper δ hδ⟩ : ↥(GammaH N H)) : SL(2, ℤ)) =
      (σ₂ * ModularGroup.T ^ (N : ℤ) * σ₂⁻¹) ^ ℓ := by
    change conjUpperMat ℓ ((uOf N H δ : ↥(GammaH N H)) : SL(2, ℤ))
      (dvd_of_mem_GammaHUpper N H ℓ ⟨uOf N H δ, uOf_mem_upper δ hδ⟩) = _
    rw [conjUpperMat_congr (coe_uOf_eq_unipMat δ) _ hdvd,
      conjUpperMat_unipMat_of_dvd_left ℓ hℓ0 hδ _ _ hdvd, conj_pow, ← zpow_natCast, ← _root_.zpow_mul,
      conj_T_zpow_eq_unipMat, hσ00, hσ10, hdiv]
  have hkey : conjL N H ℓ ⟨uOf N H δ, uOf_mem_upper δ hδ⟩ = uOf N H σ₂ ^ ℓ := by
    apply Subtype.ext; rw [hval, Subgroup.coe_pow]; rfl
  unfold termOf
  rw [hkey, ofMul_pow, map_nsmul]
  rfl

include hℓ hδ hℓN in

theorem termOf_other (φ : H1 N H A) (r : ↥(GammaH N H)) (hr : r ∉ GammaHUpper N H ℓ)
    (hmem : r⁻¹ * uOf N H δ ^ ℓ * r ∈ GammaHUpper N H ℓ) :
    ∃ σ₁ : SL(2, ℤ), σ₁ 0 0 = pOf δ r ∧ σ₁ 1 0 = ℓ * qOf δ r ∧
      termOf N H ℓ φ (r⁻¹ * uOf N H δ ^ ℓ * r) hmem = B φ σ₁ := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hp : ¬ (ℓ : ℤ) ∣ pOf δ r := fun h' => hr ((dvd_pOf_iff δ hℓ hδ r).mp h')
  have hpq : IsCoprime (pOf δ r) (qOf δ r) := isCoprime_col _
  have hpℓq : IsCoprime (pOf δ r) ((ℓ : ℤ) * qOf δ r) :=
    IsCoprime.mul_right ((Prime.coprime_iff_not_dvd hprime).mpr hp).symm hpq
  obtain ⟨σ₁, hσ00, hσ10⟩ := exists_SL2_col hpℓq
  refine ⟨σ₁, hσ00, hσ10, ?_⟩
  have hdvd : (ℓ : ℤ) ∣ (unipMat (pOf δ r) (qOf δ r) ((N : ℤ) * ℓ)) 0 1 := by
    rw [unipMat_apply_01]; exact ⟨N * pOf δ r * pOf δ r, by ring⟩
  have hval : ((conjL N H ℓ ⟨_, hmem⟩ : ↥(GammaH N H)) : SL(2, ℤ)) =
      σ₁ * ModularGroup.T ^ (N : ℤ) * σ₁⁻¹ := by
    change conjUpperMat ℓ ((r⁻¹ * uOf N H δ ^ ℓ * r : ↥(GammaH N H)) : SL(2, ℤ))
      (dvd_of_mem_GammaHUpper N H ℓ ⟨_, hmem⟩) = _
    rw [conjUpperMat_congr (coe_inv_mul_pow_mul δ r ℓ) _ hdvd,
      conjUpperMat_unipMat_of_dvd_exp ℓ hℓ0 _ _ (dvd_mul_left _ _) hdvd, conj_T_zpow_eq_unipMat, hσ00,
      hσ10, Int.mul_ediv_cancel _ hℓ0]
  have hkey : conjL N H ℓ ⟨_, hmem⟩ = uOf N H σ₁ := Subtype.ext hval
  unfold termOf
  rw [hkey]
  rfl

def ellUnit {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : (ZMod N)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)

@[scoped simp] theorem coe_ellUnit {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    ((ellUnit hℓ hℓN : (ZMod N)ˣ) : ZMod N) = ℓ := ZMod.coe_unitOfCoprime _ _

theorem ellUnit_inv_mul {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (((ellUnit hℓ hℓN)⁻¹ : (ZMod N)ˣ) : ZMod N) * (ℓ : ZMod N) = 1 := by
  rw [← coe_ellUnit hℓ hℓN, Units.inv_mul]

theorem mul_ell_cancel {N ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {x y : ZMod N}
    (h : x * (ℓ : ZMod N) = y * ℓ) : x = y := by
  have hu : IsUnit (ℓ : ZMod N) := by rw [← coe_ellUnit hℓ hℓN]; exact Units.isUnit _
  exact (IsUnit.mul_left_inj hu).mp h

include hℓ hδ hℓN in

theorem heckeT_apply_uOf (φ : H1 N H A) (σ₁ σ₂ : SL(2, ℤ))
    (hσ₂ : ((σ₂ 0 0 : ℤ) : ZMod N) * ℓ = δ 0 0 ∧ ((σ₂ 1 0 : ℤ) : ZMod N) = δ 1 0)
    (hσ₁ : ((σ₁ 0 0 : ℤ) : ZMod N) = δ 0 0 ∧ ((σ₁ 1 0 : ℤ) : ZMod N) = ℓ * δ 1 0) :
    heckeT N H ℓ A φ (Additive.ofMul (uOf N H δ)) = ℓ • B φ σ₂ + B φ σ₁ := by
  classical
  set u := uOf N H δ with hudef
  haveI : Fintype (OrbQ N H ℓ u) := Fintype.ofFinite _
  have huK : u ∈ GammaHUpper N H ℓ := uOf_mem_upper δ hδ
  have hper : ∀ O : OrbQ N H ℓ u, O ≠ orbOne N H ℓ u →
      Function.minimalPeriod (u • ·) O.out = ℓ := by
    intro O hO
    have hr : O.out.out ∉ GammaHUpper N H ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have := minimalPeriod_eq δ hℓ hδ hℓN O.out.out hr
    rwa [QuotientGroup.out_eq'] at this

  have hterm : ∀ O : OrbQ N H ℓ u, O ≠ orbOne N H ℓ u →
      termOf N H ℓ φ (O.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) O.out * O.out.out)
        (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u O.out) = B φ σ₁ := by
    intro O hO
    have hr : O.out.out ∉ GammaHUpper N H ℓ := fun hmem => hO (eq_orbOne_of_mem u O hmem)
    have hmem : O.out.out⁻¹ * u ^ ℓ * O.out.out ∈ GammaHUpper N H ℓ := by
      have := QuotientGroup.out_conj_pow_minimalPeriod_mem (GammaHUpper N H ℓ) u O.out
      rwa [hper O hO] at this
    rw [termOf_congr N H ℓ φ _ hmem (by rw [hper O hO])]
    obtain ⟨σ, hσ0, hσ1, hval⟩ := termOf_other δ hℓ hδ hℓN φ O.out.out hr hmem
    rw [hval]

    set r : ↥(GammaH N H) := O.out.out with hrdef
    obtain ⟨hr0, hrH⟩ := mem_GammaH_iff.mp r.2
    have hr10 : (((r : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hr0
    refine B_eq_of_borel φ (gamma0Units N ⟨r, hr0⟩)⁻¹ (inv_mem hrH)
      (-(((r : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) * (((ellUnit hℓ hℓN)⁻¹ : (ZMod N)ˣ) : ZMod N)) ?_ ?_
    · rw [inv_inv, colRed_fst, colRed_fst, colRed_snd, hσ0, hσ₁.1, hσ₁.2, pOf_eq]
      have e1 : ((gamma0Units N ⟨r, hr0⟩ : (ZMod N)ˣ) : ZMod N) = (((r : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) := rfl
      rw [e1]
      push_cast
      linear_combination ((((r : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) * (((δ 1 0 : ℤ)) : ZMod N)) *
        ellUnit_inv_mul hℓ hℓN
    · rw [colRed_snd, colRed_snd, hσ1, hσ₁.2, qOf_eq]
      have e2 : (((gamma0Units N ⟨r, hr0⟩)⁻¹ : (ZMod N)ˣ) : ZMod N) = (((r : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) := rfl
      rw [e2]
      push_cast
      rw [hr10]
      ring

  have hone : termOf N H ℓ φ ((orbOne N H ℓ u).out.out⁻¹ *
      u ^ Function.minimalPeriod (u • ·) (orbOne N H ℓ u).out * (orbOne N H ℓ u).out.out)
      (QuotientGroup.out_conj_pow_minimalPeriod_mem _ u _) = ℓ • B φ σ₂ := by
    have hr := orbOne_out_out_mem u huK
    have hmem : (orbOne N H ℓ u).out.out⁻¹ * u * (orbOne N H ℓ u).out.out ∈ GammaHUpper N H ℓ :=
      mul_mem (mul_mem (inv_mem hr) huK) hr
    rw [termOf_congr N H ℓ φ _ hmem (by rw [minimalPeriod_orbOne_out u huK, pow_one]),
      termOf_conj N H ℓ φ huK hr hmem]
    obtain ⟨σ, hσ0, hσ1, hval⟩ := termOf_u δ hℓ hδ φ
    rw [hval]
    congr 1
    apply B_congr
    apply Prod.ext
    · rw [colRed_fst, colRed_fst]
      apply mul_ell_cancel hℓ hℓN
      rw [hσ₂.1]
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod N)) hσ0
    · rw [colRed_snd, colRed_snd, hσ1, hσ₂.2]
  have hidx : ℓ + 1 = ∑ O : OrbQ N H ℓ u, Function.minimalPeriod (u • ·) O.out := by
    rw [← CohCarrier.index_GammaHUpper_of_prime N H ℓ hℓ hℓN]
    exact Subgroup.index_eq_sum_minimalPeriod _ u
  rw [Finset.sum_eq_add_sum_sdiff_singleton (orbOne N H ℓ u) _ (fun h => (h (Finset.mem_univ _)).elim),
    minimalPeriod_orbOne_out u huK, Finset.sum_congr rfl (fun O hO => hper O (by simpa using hO)),
    Finset.sum_const, smul_eq_mul, add_comm, Nat.add_left_cancel_iff, eq_comm,
    mul_eq_right₀ hℓ.ne_zero] at hidx
  rw [heckeT_apply_eq_sum_orbits,
    Finset.sum_eq_add_sum_sdiff_singleton (orbOne N H ℓ u) _ (fun h => (h (Finset.mem_univ _)).elim),
    hone, Finset.sum_congr rfl (fun O hO => hterm O (by simpa using hO)), Finset.sum_const, hidx,
    one_smul]

omit [NeZero ℓ] in
include hℓ hℓN in

theorem B_heckeT (φ : H1 N H A) (δ σ₁ σ₂ : SL(2, ℤ))
    (hσ₂ : ((σ₂ 0 0 : ℤ) : ZMod N) * ℓ = δ 0 0 ∧ ((σ₂ 1 0 : ℤ) : ZMod N) = δ 1 0)
    (hσ₁ : ((σ₁ 0 0 : ℤ) : ZMod N) = δ 0 0 ∧ ((σ₁ 1 0 : ℤ) : ZMod N) = ℓ * δ 1 0) :
    B (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT N H ℓ A φ) δ = ℓ • B φ σ₂ + B φ σ₁ := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨g, hg, hdvd⟩ := exists_Gamma_mul_dvd hℓ hℓN δ
  obtain ⟨hg00, hg01, hg10, hg11⟩ := Gamma_mem.mp hg
  have hg0 : g ∈ Gamma0 N := by rw [Gamma0_mem]; exact hg10
  have hcol : colRed N (g * δ) = colRed N δ := by
    rw [colRed_mul_of_mem_Gamma0 hg0, hg00, hg01, hg11]
    apply Prod.ext <;> simp
  rw [← B_congr _ hcol]
  have h0 : (((g * δ) 0 0 : ℤ) : ZMod N) = ((δ 0 0 : ℤ) : ZMod N) := congrArg Prod.fst hcol
  have h1 : (((g * δ) 1 0 : ℤ) : ZMod N) = ((δ 1 0 : ℤ) : ZMod N) := congrArg Prod.snd hcol
  exact heckeT_apply_uOf (g * δ) hℓ hdvd hℓN φ σ₁ σ₂ (by rw [h0, h1]; exact hσ₂) (by rw [h0, h1]; exact hσ₁)

theorem B_diamondL {𝒪 : Type} [CommRing 𝒪] (φ : H1 N H 𝒪) (d : (ZMod N)ˣ) (δ σ : SL(2, ℤ))
    (hσ : ((σ 0 0 : ℤ) : ZMod N) = ((d⁻¹ : (ZMod N)ˣ) : ZMod N) * δ 0 0 ∧
      ((σ 1 0 : ℤ) : ZMod N) = (d : ZMod N) * δ 1 0) :
    B (diamondL N H 𝒪 d φ) δ = B φ σ := by
  set σ₀ := Classical.choose (gamma0Units_surjective N d) with hσ₀def
  have hσ₀ : gamma0Units N σ₀ = d := Classical.choose_spec (gamma0Units_surjective N d)
  have h1 : B (diamondL N H 𝒪 d φ) δ = B φ ((σ₀ : SL(2, ℤ)) * δ) := by
    show φ (Additive.ofMul (conjHom N H σ₀ (uOf N H δ))) = φ (Additive.ofMul (uOf N H (σ₀ * δ)))
    congr 2
    apply Subtype.ext
    simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_uOf]
    group
  rw [h1]
  have hd : ((d : (ZMod N)ˣ) : ZMod N) = (((σ₀ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) := by rw [← hσ₀]; rfl
  have hdi : ((d⁻¹ : (ZMod N)ˣ) : ZMod N) = (((σ₀ : SL(2, ℤ)) 0 0 : ℤ) : ZMod N) := by rw [← hσ₀]; rfl
  refine B_eq_of_borel φ 1 (one_mem H)
    ((((σ₀ : SL(2, ℤ)) 0 1 : ℤ) : ZMod N) * ((d⁻¹ : (ZMod N)ˣ) : ZMod N)) ?_ ?_
  · rw [colRed_mul_of_mem_Gamma0 σ₀.2, colRed_fst, colRed_snd, hσ.1, hσ.2, inv_one, Units.val_one,
      one_mul, ← hdi, mul_assoc _ ((d⁻¹ : (ZMod N)ˣ) : ZMod N), ← mul_assoc ((d⁻¹ : (ZMod N)ˣ) : ZMod N),
      Units.inv_mul, one_mul]
  · rw [colRed_mul_of_mem_Gamma0 σ₀.2, colRed_snd, hσ.2, Units.val_one, one_mul, hd]

end Hecke

section Parabolic

variable {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}

theorem mem_parabolicHoms_of_B_eq_zero (φ : H1 N H ℂ) (hB : ∀ δ : SL(2, ℤ), B φ δ = 0) :
    φ ∈ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff]
  intro γ hγ
  obtain ⟨ε, δ, h, hε, hγeq⟩ :=
    ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
  have hcomm : Commute ε (δ * ModularGroup.T ^ h * δ⁻¹) := by
    rcases hε with rfl | rfl
    · exact Commute.one_left _
    · rw [Commute, SemiconjBy, neg_one_mul, mul_neg_one]
  have hε2 : ε ^ (2 * N) = 1 := by
    rcases hε with rfl | rfl
    · exact one_pow _
    · rw [pow_mul, sq, neg_mul_neg, one_mul, one_pow]
  have hpow : γ ^ (2 * N) = (uOf N H δ) ^ (2 * h) := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_zpow, hγeq, coe_uOf, hcomm.mul_pow, hε2, one_mul, conj_pow,
      conj_zpow, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul,
      show h * ((2 * N : ℕ) : ℤ) = (N : ℤ) * (2 * h) by push_cast; ring]
  have h1 : φ (Additive.ofMul (γ ^ (2 * N))) = (2 * N) • φ (Additive.ofMul γ) := by
    rw [ofMul_pow, map_nsmul]
  have h2 : φ (Additive.ofMul ((uOf N H δ) ^ (2 * h))) = (2 * h) • B φ δ := by
    rw [ofMul_zpow, map_zsmul]; rfl
  rw [hpow, h2, hB, smul_zero] at h1
  have h3 : (2 * N) • φ (Additive.ofMul γ) = 0 := h1.symm
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (mul_ne_zero two_ne_zero (NeZero.ne N))
  · exact h4

end Parabolic

section Boundary

variable (N : ℕ) [NeZero N]

def P : Type := {v : ZMod N × ZMod N // IsCoprime v.1 v.2}

scoped instance : Finite (P N) := by unfold P; infer_instance

variable {N}

theorem exists_lift (p : P N) : ∃ δ : SL(2, ℤ), colRed N δ = p.1 := by
  obtain ⟨g, hg0, hg1⟩ := p.2.exists_SL2_col 0
  obtain ⟨δ, hδ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod N g
  refine ⟨δ, ?_⟩
  have e : ∀ i j, ((δ i j : ℤ) : ZMod N) = g i j := fun i j => by
    have := congrArg (fun x : SL(2, ZMod N) => x i j) hδ
    simpa using this
  exact Prod.ext ((e 0 0).trans hg0) ((e 1 0).trans hg1)

noncomputable def lift (p : P N) : SL(2, ℤ) := Classical.choose (exists_lift p)

theorem colRed_lift (p : P N) : colRed N (lift p) = p.1 := Classical.choose_spec (exists_lift p)

def toP (δ : SL(2, ℤ)) : P N :=
  ⟨colRed N δ, by
    obtain ⟨x, y, hxy⟩ := isCoprime_col δ
    refine ⟨(x : ZMod N), (y : ZMod N), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod N)) hxy
    push_cast at this
    exact this⟩

def scale (x y : (ZMod N)ˣ) (p : P N) : P N :=
  ⟨((x : ZMod N) * p.1.1, (y : ZMod N) * p.1.2),
    (isCoprime_mul_unit_left_left x.isUnit _ _).mpr
      ((isCoprime_mul_unit_left_right y.isUnit _ _).mpr p.2)⟩

@[scoped simp] theorem scale_val_fst (x y : (ZMod N)ˣ) (p : P N) : (scale x y p).1.1 = (x : ZMod N) * p.1.1 := rfl
@[scoped simp] theorem scale_val_snd (x y : (ZMod N)ˣ) (p : P N) : (scale x y p).1.2 = (y : ZMod N) * p.1.2 := rfl

theorem scale_scale (x y x' y' : (ZMod N)ˣ) (p : P N) :
    scale x y (scale x' y' p) = scale (x * x') (y * y') p := by
  apply Subtype.ext
  apply Prod.ext <;> simp [mul_assoc]

theorem scale_comm (x y x' y' : (ZMod N)ˣ) (p : P N) :
    scale x y (scale x' y' p) = scale x' y' (scale x y p) := by
  rw [scale_scale, scale_scale, mul_comm x, mul_comm y]

theorem scale_one (p : P N) : scale 1 1 p = p := by
  apply Subtype.ext
  apply Prod.ext <;> simp

variable {H : Subgroup (ZMod N)ˣ} {A : Type*} [AddCommGroup A]

noncomputable def bOf (φ : H1 N H A) (p : P N) : A := B φ (lift p)

theorem bOf_toP (φ : H1 N H A) (δ : SL(2, ℤ)) : bOf φ (toP δ) = B φ δ :=
  B_congr φ (colRed_lift _)

theorem bOf_smul {R : Type*} [Semiring R] [Module R A] (c : R) (φ : H1 N H A) (p : P N) :
    bOf (c • φ) p = c • bOf φ p := rfl

theorem bOf_heckeT {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : H1 N H A) (p : P N) :
    bOf (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT N H ℓ A φ) p =
      ℓ • bOf φ (scale (ellUnit hℓ hℓN)⁻¹ 1 p) + bOf φ (scale 1 (ellUnit hℓ hℓN) p) := by
  unfold bOf
  have h0 : ∀ q : P N, (((lift q) 0 0 : ℤ) : ZMod N) = q.1.1 := fun q => congrArg Prod.fst (colRed_lift q)
  have h1 : ∀ q : P N, (((lift q) 1 0 : ℤ) : ZMod N) = q.1.2 := fun q => congrArg Prod.snd (colRed_lift q)
  refine B_heckeT hℓ hℓN φ (lift p) (lift (scale 1 (ellUnit hℓ hℓN) p))
    (lift (scale (ellUnit hℓ hℓN)⁻¹ 1 p)) ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rw [h0, h0, scale_val_fst, mul_comm, ← mul_assoc, ← coe_ellUnit hℓ hℓN, Units.mul_inv, one_mul]
  · rw [h1, h1, scale_val_snd, Units.val_one, one_mul]
  · rw [h0, h0, scale_val_fst, Units.val_one, one_mul]
  · rw [h1, h1, scale_val_snd, coe_ellUnit]

theorem bOf_diamondL {𝒪 : Type} [CommRing 𝒪] (φ : H1 N H 𝒪) (d : (ZMod N)ˣ) (p : P N) :
    bOf (diamondL N H 𝒪 d φ) p = bOf φ (scale d⁻¹ d p) := by
  unfold bOf
  apply B_diamondL
  refine ⟨?_, ?_⟩
  · rw [show (((lift (scale d⁻¹ d p)) 0 0 : ℤ) : ZMod N) = _ from congrArg Prod.fst (colRed_lift _),
      show (((lift p) 0 0 : ℤ) : ZMod N) = _ from congrArg Prod.fst (colRed_lift _), scale_val_fst]
  · rw [show (((lift (scale d⁻¹ d p)) 1 0 : ℤ) : ZMod N) = _ from congrArg Prod.snd (colRed_lift _),
      show (((lift p) 1 0 : ℤ) : ZMod N) = _ from congrArg Prod.snd (colRed_lift _), scale_val_snd]

theorem bOf_ne_zero (φ : H1 N H ℂ)
    (hφ : φ ∉ ModularCurve.Period.parabolicHoms ℂ (GammaH N H) ℂ) : bOf φ ≠ 0 := by
  intro h
  apply hφ
  apply mem_parabolicHoms_of_B_eq_zero
  intro δ
  rw [← bOf_toP φ δ, h]
  rfl

variable (S : Set ℕ) (a : ℕ → ℂ) (e : (ZMod N)ˣ →* ℂˣ)

def W : Submodule ℂ (P N → ℂ) where
  carrier := {f | (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (hℓN : ¬ ℓ ∣ N) (p : P N),
      (ℓ : ℂ) * f (scale (ellUnit hℓ hℓN)⁻¹ 1 p) + f (scale 1 (ellUnit hℓ hℓN) p) = a ℓ * f p) ∧
    (∀ (d : (ZMod N)ˣ) (p : P N), f (scale d⁻¹ d p) = (e d : ℂ) * f p)}
  zero_mem' := ⟨fun _ _ _ _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun ℓ hℓ hS hℓN p => ?_, fun d p => ?_⟩
    · simp only [Pi.add_apply]
      linear_combination hf1 ℓ hℓ hS hℓN p + hg1 ℓ hℓ hS hℓN p
    · simp only [Pi.add_apply]
      rw [hf2, hg2]; ring
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨fun ℓ hℓ hS hℓN p => ?_, fun d p => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination c * hf1 ℓ hℓ hS hℓN p
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hf2]; ring

noncomputable def ρ (g : (ZMod N)ˣ × (ZMod N)ˣ) : (P N → ℂ) →ₗ[ℂ] (P N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (scale g.1 g.2)

@[scoped simp] theorem ρ_apply (g : (ZMod N)ˣ × (ZMod N)ˣ) (f : P N → ℂ) (p : P N) :
    ρ g f p = f (scale g.1 g.2 p) := rfl

theorem ρ_mem_W (g : (ZMod N)ˣ × (ZMod N)ˣ) {f : P N → ℂ} (hf : f ∈ W S a e) : ρ g f ∈ W S a e := by
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨fun ℓ hℓ hS hℓN p => ?_, fun d p => ?_⟩
  · simp only [ρ_apply]
    rw [scale_comm, scale_comm g.1, hf1 ℓ hℓ hS hℓN]
  · simp only [ρ_apply]
    rw [scale_comm, hf2]

noncomputable def ρW (g : (ZMod N)ˣ × (ZMod N)ˣ) : Module.End ℂ ↥(W S a e) :=
  (ρ g).restrict (fun _ hf => ρ_mem_W S a e g hf)

theorem ρW_comm (g g' : (ZMod N)ˣ × (ZMod N)ˣ) : Commute (ρW S a e g) (ρW S a e g') := by
  ext ⟨f, hf⟩ p
  simp only [ρW, Module.End.mul_apply, LinearMap.restrict_apply, ρ_apply]
  rw [scale_comm]

end Boundary

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∉ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)
    (a : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ ψ₁ ψ₂ : DirichletCharacter ℂ M,
      (∀ u : (ZMod M)ˣ, ψ₁ (u : ZMod M) * ψ₂ (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M →
        a ℓ = ψ₁ (ℓ : ZMod M) + (ℓ : ℂ) * ψ₂ (ℓ : ZMod M)) := by
  classical

  set b : P M → ℂ := bOf φ with hbdef
  have hb0 : b ≠ 0 := bOf_ne_zero φ hφpar
  have hbW : b ∈ W S a e := by
    refine ⟨fun ℓ hℓ hS hℓN p => ?_, fun d p => ?_⟩
    · have h := bOf_heckeT hℓ hℓN φ p
      rw [hT ℓ hℓ hS hℓN, bOf_smul, smul_eq_mul, nsmul_eq_mul] at h
      exact h.symm
    · have h := bOf_diamondL φ d p
      rw [hD d, bOf_smul, smul_eq_mul] at h
      exact h.symm
  haveI : Nontrivial ↥(W S a e) :=
    nontrivial_of_ne (⟨b, hbW⟩ : ↥(W S a e)) 0 (fun h => hb0 (congrArg Subtype.val h))
  haveI : Fintype (P M) := Fintype.ofFinite _

  obtain ⟨χ, w, hw0, hw⟩ :=
    Module.End.exists_common_eigenvector_of_commute (ρW S a e) (ρW_comm S a e)
  set f : P M → ℂ := (w : P M → ℂ) with hfdef
  have hf : ∀ (g : (ZMod M)ˣ × (ZMod M)ˣ) (p : P M), f (scale g.1 g.2 p) = χ g * f p := by
    intro g p
    have := congrArg (fun v : ↥(W S a e) => (v : P M → ℂ) p) (hw g)
    simpa [ρW, hfdef] using this
  have hfW : f ∈ W S a e := w.2
  have hf0 : f ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hf0
  simp only [Pi.zero_apply] at hp₀

  have hχmul : ∀ g g', χ (g * g') = χ g * χ g' := by
    intro g g'
    have h1 := hf (g * g') p₀
    rw [Prod.fst_mul, Prod.snd_mul, ← scale_scale, hf g, hf g', ← mul_assoc] at h1
    exact (mul_right_cancel₀ hp₀ h1).symm
  have hχone : χ 1 = 1 := by
    have h1 := hf 1 p₀
    rw [Prod.fst_one, Prod.snd_one, scale_one] at h1
    exact ((mul_eq_right₀ hp₀).mp h1.symm)
  have hχne : ∀ g, χ g ≠ 0 := fun g => by
    have := hχmul g g⁻¹
    rw [mul_inv_cancel, hχone] at this
    exact left_ne_zero_of_mul_eq_one this.symm
  let χu : (ZMod M)ˣ × (ZMod M)ˣ →* ℂˣ :=
    { toFun := fun g => Units.mk0 (χ g) (hχne g)
      map_one' := Units.ext hχone
      map_mul' := fun g g' => Units.ext (hχmul g g') }
  have hχu : ∀ g, ((χu g : ℂˣ) : ℂ) = χ g := fun g => rfl

  let ψ₁ : DirichletCharacter ℂ M := MulChar.ofUnitHom (χu.comp (MonoidHom.inr _ _))
  let ψ₂ : DirichletCharacter ℂ M :=
    MulChar.ofUnitHom (χu.comp ((MonoidHom.inl _ _).comp invMonoidHom))
  have hψ₁ : ∀ u : (ZMod M)ˣ, ψ₁ (u : ZMod M) = χ (1, u) := fun u => by
    show (MulChar.ofUnitHom (χu.comp (MonoidHom.inr _ _))) (u : ZMod M) = χ (1, u)
    rw [MulChar.ofUnitHom_coe]; rfl
  have hψ₂ : ∀ u : (ZMod M)ˣ, ψ₂ (u : ZMod M) = χ (u⁻¹, 1) := fun u => by
    show (MulChar.ofUnitHom (χu.comp ((MonoidHom.inl _ _).comp invMonoidHom))) (u : ZMod M) = χ (u⁻¹, 1)
    rw [MulChar.ofUnitHom_coe]; rfl
  refine ⟨ψ₁, ψ₂, fun u => ?_, fun ℓ hℓ hS hℓN => ?_⟩
  ·
    rw [hψ₁, hψ₂, ← hχmul, show ((1 : (ZMod M)ˣ), u) * (u⁻¹, 1) = (u⁻¹, u) from
      Prod.ext (one_mul _) (mul_one _)]
    have h1 := hfW.2 u p₀
    rw [show scale u⁻¹ u p₀ = scale (u⁻¹, u).1 (u⁻¹, u).2 p₀ from rfl, hf] at h1
    exact mul_right_cancel₀ hp₀ h1
  ·
    rw [← coe_ellUnit hℓ hℓN, hψ₁, hψ₂]
    have h1 := hfW.1 ℓ hℓ hS hℓN p₀
    rw [show scale (ellUnit hℓ hℓN)⁻¹ 1 p₀ = scale ((ellUnit hℓ hℓN)⁻¹, (1 : (ZMod M)ˣ)).1
        ((ellUnit hℓ hℓN)⁻¹, (1 : (ZMod M)ˣ)).2 p₀ from rfl, hf,
      show scale 1 (ellUnit hℓ hℓN) p₀ = scale ((1 : (ZMod M)ˣ), ellUnit hℓ hℓN).1
        ((1 : (ZMod M)ˣ), ellUnit hℓ hℓN).2 p₀ from rfl, hf] at h1
    have h2 : (χ (1, ellUnit hℓ hℓN) + (ℓ : ℂ) * χ ((ellUnit hℓ hℓN)⁻¹, 1)) * f p₀ = a ℓ * f p₀ := by
      linear_combination h1
    exact (mul_right_cancel₀ hp₀ h2).symm

end CohCarrier.BdryEis
p2m_reactivate "P2MW.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul.CohCarrier P2MW.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul.CohCarrier.BdryEis"
p2m_reactivate "P2MW.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul.CohCarrier"

open CohCarrier.BdryEis in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (φ : CohCarrier.H1 M H ℂ)
    (hφpar : φ ∉ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)
    (a : ℕ → ℂ) (e : (ZMod M)ˣ →* ℂˣ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ¬ ℓ ∣ M →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ ℂ φ) = a ℓ • φ)
    (hD : ∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H ℂ u φ = (e u : ℂ) • φ) :
    ∃ ψ₁ ψ₂ : DirichletCharacter ℂ M,
      (∀ u : (ZMod M)ˣ, ψ₁ (u : ZMod M) * ψ₂ (u : ZMod M) = e u) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ¬ ℓ ∣ M →
        a ℓ = ψ₁ (ℓ : ZMod M) + (ℓ : ℂ) * ψ₂ (ℓ : ZMod M)) :=
  main M H S φ hφpar a e hT hD

end S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul
end P2MW
export P2MW.S_CohCarrier_exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul (solution)
