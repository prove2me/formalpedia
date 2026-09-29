-- Prove2me | solution 1 for CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0e69dbd4-df31-57e7-b719-613c30bb40cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace GammaGenSol

open Matrix MatrixGroups CongruenceSubgroup Matrix.SpecialLinearGroup

def Low (x : ℤ) : SL(2, ℤ) := ⟨!![1, 0; x, 1], by rw [Matrix.det_fin_two_of]; ring⟩

def Up (x : ℤ) : SL(2, ℤ) := ⟨!![1, x; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] lemma coe_Low (x : ℤ) : (Low x : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; x, 1] := rfl
@[scoped simp] lemma coe_Up (x : ℤ) : (Up x : Matrix (Fin 2) (Fin 2) ℤ) = !![1, x; 0, 1] := rfl

lemma Low_apply (x : ℤ) (i j : Fin 2) : (Low x) i j = !![(1 : ℤ), 0; x, 1] i j := rfl
lemma Up_apply (x : ℤ) (i j : Fin 2) : (Up x) i j = !![(1 : ℤ), x; 0, 1] i j := rfl

lemma Low_add (x y : ℤ) : Low (x + y) = Low x * Low y := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Low, coe_Low, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma Low_zero : Low 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma Low_neg (x : ℤ) : Low (-x) = (Low x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← Low_add, neg_add_cancel, Low_zero]

lemma Low_natMul (x : ℤ) (n : ℕ) : Low (n * x) = Low x ^ n := by
  induction n with
  | zero => simp [Low_zero]
  | succ n ih => rw [pow_succ, ← ih, ← Low_add]; congr 1; push_cast; ring

lemma Low_intMul (x : ℤ) (n : ℤ) : Low (n * x) = Low x ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, Low_natMul]
  · rw [_root_.zpow_neg, zpow_natCast, ← Low_natMul, ← Low_neg]; congr 1; ring

lemma Up_eq_T_zpow (x : ℤ) : Up x = ModularGroup.T ^ x := by
  ext i j
  rw [coe_Up, ModularGroup.coe_T_zpow]

lemma S_T_S_eq (n : ℤ) : ModularGroup.S * ModularGroup.T ^ n * ModularGroup.S⁻¹ = Low (-n) := by
  ext i j
  rw [ModularGroup.S_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
    ModularGroup.coe_S, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

section entries

variable (x : ℤ) (m : SL(2, ℤ))

lemma Up_mul_apply (i j : Fin 2) :
    (Up x * m) i j = !![m 0 0 + x * m 1 0, m 0 1 + x * m 1 1; m 1 0, m 1 1] i j := by
  show ((Up x * m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Up]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_Low_apply (i j : Fin 2) :
    (m * Low x) i j = !![m 0 0 + m 0 1 * x, m 0 1; m 1 0 + m 1 1 * x, m 1 1] i j := by
  show ((m * Low x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma mul_Up_apply (i j : Fin 2) :
    (m * Up x) i j = !![m 0 0, m 0 0 * x + m 0 1; m 1 0, m 1 0 * x + m 1 1] i j := by
  show ((m * Up x : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Up]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma Low_mul_apply (i j : Fin 2) :
    (Low x * m) i j = !![m 0 0, m 0 1; m 1 0 + x * m 0 0, m 1 1 + x * m 0 1] i j := by
  show ((Low x * m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_Low]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end entries

lemma det_eq (m : SL(2, ℤ)) : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by
  have := m.det_coe; rwa [Matrix.det_fin_two] at this

lemma mem_Gamma_iff (n : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ Gamma n ↔ (n : ℤ) ∣ γ 0 0 - 1 ∧ (n : ℤ) ∣ γ 0 1 ∧ (n : ℤ) ∣ γ 1 0 ∧ (n : ℤ) ∣ γ 1 1 - 1 := by
  rw [Gamma_mem]
  have h1 : ∀ x : ℤ, ((x : ℤ) : ZMod n) = 1 ↔ (n : ℤ) ∣ x - 1 := fun x => by
    rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [h1, h1, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma Gamma_le_Gamma_of_dvd {A B : ℕ} (h : A ∣ B) : Gamma B ≤ Gamma A := by
  intro γ hγ
  rw [mem_Gamma_iff] at hγ ⊢
  have hAB : (A : ℤ) ∣ (B : ℤ) := Int.natCast_dvd_natCast.mpr h
  exact ⟨hAB.trans hγ.1, hAB.trans hγ.2.1, hAB.trans hγ.2.2.1, hAB.trans hγ.2.2.2⟩

lemma Gamma_le_Gamma1 (n : ℕ) : Gamma n ≤ Gamma1 n := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

lemma Low_mem_Gamma_of_dvd {n : ℕ} {x : ℤ} (h : (n : ℤ) ∣ x) : Low x ∈ Gamma n := by
  rw [mem_Gamma_iff]; simp [Low_apply, h]

lemma Up_mem_Gamma_of_dvd {n : ℕ} {x : ℤ} (h : (n : ℤ) ∣ x) : Up x ∈ Gamma n := by
  rw [mem_Gamma_iff]; simp [Up_apply, h]

lemma Up_mem_Gamma1 (n : ℕ) (x : ℤ) : Up x ∈ Gamma1 n := by
  rw [Gamma1_mem]; simp [Up_apply]

lemma mul_inv_mem_Gamma {n : ℕ} {x y : SL(2, ℤ)} (h : ∀ i j, (n : ℤ) ∣ y i j - x i j) :
    x * y⁻¹ ∈ Gamma n := by
  have hxy : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) x)
      = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n)) y := by
    ext i j
    rw [SL_reduction_mod_hom_val, SL_reduction_mod_hom_val, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact h i j
  rw [Gamma_mem', map_mul, map_inv, hxy, mul_inv_cancel]

section Main

variable {N p : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N)

def G (N p : ℕ) : Subgroup SL(2, ℤ) :=
  (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
    Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹)

lemma Low_mem_G (t : ℤ) : Low (t * ((N / p : ℕ) : ℤ)) ∈ G N p := by
  apply Subgroup.mem_sup_right
  rw [S_T_S_eq, show t * ((N / p : ℕ) : ℤ) = (-t) * (-((N / p : ℕ) : ℤ)) by ring, Low_intMul]
  exact Subgroup.zpow_mem_zpowers _ _

lemma Low_mem_G_of_dvd {x : ℤ} (hx : (((N / p : ℕ) : ℤ)) ∣ x) : Low x ∈ G N p := by
  obtain ⟨t, rfl⟩ := hx
  rw [mul_comm]; exact Low_mem_G t

lemma Up_mem_G {x : ℤ} (hx : ((N / p ^ N.factorization p : ℕ) : ℤ) ∣ x) : Up x ∈ G N p :=
  Subgroup.mem_sup_left ⟨Up_mem_Gamma1 N x, Up_mem_Gamma_of_dvd hx⟩

lemma Gamma_le_G : Gamma N ≤ G N p := fun γ hγ =>
  Subgroup.mem_sup_left ⟨Gamma_le_Gamma1 N hγ,
    Gamma_le_Gamma_of_dvd (Nat.ordCompl_dvd N p) hγ⟩

include hp hpN

lemma setup :
    let q := p ^ N.factorization p
    let M := N / p ^ N.factorization p
    q * M = N ∧ (N / p) * p = N ∧ M ∣ N / p ∧ Nat.Coprime q M ∧ ¬ p ∣ M ∧ q ∣ N ∧ p ∣ q := by
  have hN : N ≠ 0 := NeZero.ne N
  have he : 0 < N.factorization p := hp.factorization_pos_of_dvd hN hpN
  refine ⟨Nat.ordProj_mul_ordCompl_eq_self N p, Nat.div_mul_cancel hpN, ?_, ?_,
    Nat.not_dvd_ordCompl hp hN, Nat.ordProj_dvd N p, dvd_pow_self p he.ne'⟩
  ·
    refine ⟨p ^ (N.factorization p - 1), ?_⟩
    have h1 : N = (N / p ^ N.factorization p) * p ^ N.factorization p :=
      (Nat.ordProj_mul_ordCompl_eq_self N p).symm.trans (mul_comm _ _)
    conv_lhs => rw [h1]
    rw [show p ^ N.factorization p = p ^ (N.factorization p - 1) * p by
      rw [← pow_succ, Nat.sub_add_cancel he], ← mul_assoc, Nat.mul_div_cancel _ hp.pos]
  · exact (Nat.coprime_ordCompl hp hN).pow_left _

lemma mem_G_of_not_dvd (m : SL(2, ℤ)) (hm : m ∈ Gamma (N / p)) (hd : ¬ (p : ℤ) ∣ m 1 1) :
    m ∈ G N p := by
  obtain ⟨hqM, hNp, hMN', hcop, hpM, hqN, hpq⟩ := setup hp hpN
  set q : ℕ := p ^ N.factorization p with hqdef
  set M : ℕ := N / p ^ N.factorization p with hMdef
  set N' : ℕ := N / p with hN'def
  haveI : Fact p.Prime := ⟨hp⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNZ : (N : ℤ) = (N' : ℤ) * p := by exact_mod_cast hNp.symm
  have hNqM : (N : ℤ) = (q : ℤ) * M := by exact_mod_cast hqM.symm
  have hMN'Z : (M : ℤ) ∣ (N' : ℤ) := Int.natCast_dvd_natCast.mpr hMN'
  have hqNZ : (q : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr hqN
  have hN'N : (N' : ℤ) ∣ (N : ℤ) := ⟨p, hNZ⟩
  have hMNZ : (M : ℤ) ∣ (N : ℤ) := hMN'Z.trans hN'N
  obtain ⟨ha, hb, hc, hdd⟩ := (mem_Gamma_iff _ _).mp hm

  obtain ⟨c', hc'⟩ := hc
  have hd0 : ((m 1 1 : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set t : ℤ := -((((c' : ℤ) : ZMod p) * ((m 1 1 : ℤ) : ZMod p)⁻¹).val : ℤ) with htdef
  have ht : (p : ℤ) ∣ c' + m 1 1 * t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, htdef]
    push_cast
    rw [ZMod.natCast_zmod_val, mul_neg, mul_comm (((m 1 1 : ℤ) : ZMod p)), mul_assoc,
      inv_mul_cancel₀ hd0, mul_one, add_neg_cancel]
  set m₂ : SL(2, ℤ) := m * Low ((N' : ℤ) * t) with hm₂def
  have hm₂G : m₂ ∈ G N p ↔ m ∈ G N p := by
    rw [hm₂def]
    refine ⟨fun h => ?_, fun h => mul_mem h (Low_mem_G_of_dvd ⟨t, rfl⟩)⟩
    have := mul_mem h (inv_mem (Low_mem_G_of_dvd (N := N) (p := p) ⟨t, rfl⟩))
    rwa [mul_inv_cancel_right] at this
  rw [← hm₂G]

  have e₂00 : m₂ 0 0 = m 0 0 + m 0 1 * (N' * t) := by rw [hm₂def, mul_Low_apply]; rfl
  have e₂01 : m₂ 0 1 = m 0 1 := by rw [hm₂def, mul_Low_apply]; rfl
  have e₂10 : m₂ 1 0 = m 1 0 + m 1 1 * (N' * t) := by rw [hm₂def, mul_Low_apply]; rfl
  have e₂11 : m₂ 1 1 = m 1 1 := by rw [hm₂def, mul_Low_apply]; rfl
  have hc₂ : (N : ℤ) ∣ m₂ 1 0 := by
    rw [e₂10, hc', hNZ]
    have : (N' : ℤ) * c' + m 1 1 * (N' * t) = N' * (c' + m 1 1 * t) := by ring
    rw [this]
    exact mul_dvd_mul_left _ ht
  have hb₂ : (N' : ℤ) ∣ m₂ 0 1 := by rw [e₂01]; exact hb
  have ha₂ : (N' : ℤ) ∣ m₂ 0 0 - 1 := by
    rw [e₂00]
    have : m 0 0 + m 0 1 * (N' * t) - 1 = (m 0 0 - 1) + N' * (m 0 1 * t) := by ring
    rw [this]; exact dvd_add ha (dvd_mul_right _ _)
  have hd₂ : (N' : ℤ) ∣ m₂ 1 1 - 1 := by rw [e₂11]; exact hdd
  have hd₂p : ¬ (p : ℤ) ∣ m₂ 1 1 := by rw [e₂11]; exact hd
  have hdet₂ := det_eq m₂

  set β : ℤ := -(m₂ 0 1 * m₂ 0 0) with hβdef
  have hβM : (M : ℤ) ∣ β := by
    rw [hβdef]; exact (dvd_mul_of_dvd_left (hMN'Z.trans hb₂) _).neg_right
  set m₃ : SL(2, ℤ) := Up β * m₂ with hm₃def
  have hm₃G : m₃ ∈ G N p ↔ m₂ ∈ G N p := by
    rw [hm₃def]
    refine ⟨fun h => ?_, fun h => mul_mem (Up_mem_G hβM) h⟩
    have := mul_mem (inv_mem (Up_mem_G (N := N) (p := p) hβM)) h
    rwa [inv_mul_cancel_left] at this
  rw [← hm₃G]
  have e₃00 : m₃ 0 0 = m₂ 0 0 + β * m₂ 1 0 := by rw [hm₃def, Up_mul_apply]; rfl
  have e₃01 : m₃ 0 1 = m₂ 0 1 + β * m₂ 1 1 := by rw [hm₃def, Up_mul_apply]; rfl
  have e₃10 : m₃ 1 0 = m₂ 1 0 := by rw [hm₃def, Up_mul_apply]; rfl
  have e₃11 : m₃ 1 1 = m₂ 1 1 := by rw [hm₃def, Up_mul_apply]; rfl
  have hb₃ : (N : ℤ) ∣ m₃ 0 1 := by
    rw [e₃01, hβdef]
    have : m₂ 0 1 + -(m₂ 0 1 * m₂ 0 0) * m₂ 1 1 = -(m₂ 0 1 * m₂ 0 1) * m₂ 1 0 := by
      linear_combination (-(m₂ 0 1)) * hdet₂
    rw [this]; exact dvd_mul_of_dvd_right hc₂ _
  have hc₃ : (N : ℤ) ∣ m₃ 1 0 := by rw [e₃10]; exact hc₂
  have ha₃ : (N' : ℤ) ∣ m₃ 0 0 - 1 := by
    rw [e₃00]
    have : m₂ 0 0 + β * m₂ 1 0 - 1 = (m₂ 0 0 - 1) + β * m₂ 1 0 := by ring
    rw [this]; exact dvd_add ha₂ (dvd_mul_of_dvd_right (hN'N.trans hc₂) _)
  have hd₃ : (N' : ℤ) ∣ m₃ 1 1 - 1 := by rw [e₃11]; exact hd₂
  have hdet₃ := det_eq m₃
  have had₃ : (N : ℤ) ∣ m₃ 0 0 * m₃ 1 1 - 1 := by
    have : m₃ 0 0 * m₃ 1 1 - 1 = m₃ 0 1 * m₃ 1 0 := by linear_combination hdet₃
    rw [this]; exact dvd_mul_of_dvd_left hb₃ _

  set u : ℤ := (M : ℤ) * ((((M : ZMod q))⁻¹).val : ℤ) with hudef
  haveI : NeZero q := ⟨pow_ne_zero _ hp.ne_zero⟩
  have huq : (q : ℤ) ∣ u - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hudef]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.coe_mul_inv_eq_one M hcop.symm, sub_self]
  have huM : (M : ℤ) ∣ u := ⟨_, rfl⟩
  set a₃ : ℤ := m₃ 0 0 with ha₃def
  set d₃ : ℤ := m₃ 1 1 with hd₃def
  set β₂ : ℤ := a₃ * u with hβ₂def
  set β₁ : ℤ := -u with hβ₁def
  set P : SL(2, ℤ) := Up β₂ * Low (1 - d₃) * Up β₁ * Low (1 - a₃) with hPdef
  have hLd : Low (1 - d₃) ∈ G N p := Low_mem_G_of_dvd (by
    have : 1 - d₃ = -(d₃ - 1) := by ring
    rw [this]; exact hd₃.neg_right)
  have hLa : Low (1 - a₃) ∈ G N p := Low_mem_G_of_dvd (by
    have : 1 - a₃ = -(a₃ - 1) := by ring
    rw [this]; exact ha₃.neg_right)
  have hβ₂M : (M : ℤ) ∣ β₂ := dvd_mul_of_dvd_right huM _
  have hβ₁M : (M : ℤ) ∣ β₁ := huM.neg_right
  have hPG : P ∈ G N p :=
    mul_mem (mul_mem (mul_mem (Up_mem_G hβ₂M) hLd) (Up_mem_G hβ₁M)) hLa

  have eP01 : P 0 1 = β₁ * (1 + β₂ * (1 - d₃)) + β₂ := by
    simp only [hPdef, Up_mul_apply, mul_Up_apply, Low_mul_apply, mul_Low_apply, Low_apply,
      Up_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring
  have eP11 : P 1 1 = β₁ * (1 - d₃) + 1 := by
    simp only [hPdef, Up_mul_apply, mul_Up_apply, Low_mul_apply, mul_Low_apply, Low_apply,
      Up_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring
  have eP00 : P 0 0 = (1 + β₂ * (1 - d₃)) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) := by
    simp only [hPdef, Up_mul_apply, mul_Up_apply, Low_mul_apply, mul_Low_apply, Low_apply,
      Up_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring
  have eP10 : P 1 0 = (1 - d₃) + (β₁ * (1 - d₃) + 1) * (1 - a₃) := by
    simp only [hPdef, Up_mul_apply, mul_Up_apply, Low_mul_apply, mul_Low_apply, Low_apply,
      Up_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    ring

  have hqβ₁ : (q : ℤ) ∣ β₁ + 1 := by
    rw [hβ₁def, show -u + 1 = -(u - 1) by ring]; exact huq.neg_right
  have hqβ₂ : (q : ℤ) ∣ β₂ - a₃ := by
    rw [hβ₂def, show a₃ * u - a₃ = a₃ * (u - 1) by ring]; exact dvd_mul_of_dvd_right huq _
  have hqad : (q : ℤ) ∣ a₃ * d₃ - 1 := hqNZ.trans had₃
  have hq00 : (q : ℤ) ∣ P 0 0 - m₃ 0 0 := by
    rw [eP00, ← ha₃def]
    have : (1 + β₂ * (1 - d₃)) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) - a₃
        = -(a₃ * d₃ - 1) + (β₂ - a₃) * (1 - d₃)
          + ((a₃ * d₃ - 1) + (β₂ - a₃) * d₃ + (β₁ + 1) * (1 + β₂ * (1 - d₃))) * (1 - a₃) := by
      ring
    rw [this]
    refine dvd_add (dvd_add hqad.neg_right (dvd_mul_of_dvd_left hqβ₂ _)) ?_
    exact dvd_mul_of_dvd_left (dvd_add (dvd_add hqad (dvd_mul_of_dvd_left hqβ₂ _))
      (dvd_mul_of_dvd_left hqβ₁ _)) _
  have hq01 : (q : ℤ) ∣ P 0 1 - m₃ 0 1 := by
    rw [eP01]
    have : β₁ * (1 + β₂ * (1 - d₃)) + β₂ - m₃ 0 1
        = (a₃ * d₃ - 1) + (β₂ - a₃) * d₃ + (β₁ + 1) * (1 + β₂ * (1 - d₃)) - m₃ 0 1 := by ring
    rw [this]
    exact dvd_sub (dvd_add (dvd_add hqad (dvd_mul_of_dvd_left hqβ₂ _))
      (dvd_mul_of_dvd_left hqβ₁ _)) (hqNZ.trans hb₃)
  have hq10 : (q : ℤ) ∣ P 1 0 - m₃ 1 0 := by
    rw [eP10]
    have : (1 - d₃) + (β₁ * (1 - d₃) + 1) * (1 - a₃) - m₃ 1 0
        = -(a₃ * d₃ - 1) + (β₁ + 1) * ((1 - d₃) * (1 - a₃)) - m₃ 1 0 := by ring
    rw [this]
    exact dvd_sub (dvd_add hqad.neg_right (dvd_mul_of_dvd_left hqβ₁ _)) (hqNZ.trans hc₃)
  have hq11 : (q : ℤ) ∣ P 1 1 - m₃ 1 1 := by
    rw [eP11, ← hd₃def]
    have : β₁ * (1 - d₃) + 1 - d₃ = (β₁ + 1) * (1 - d₃) := by ring
    rw [this]; exact dvd_mul_of_dvd_left hqβ₁ _

  have hMa : (M : ℤ) ∣ 1 - a₃ := by
    have : 1 - a₃ = -(a₃ - 1) := by ring
    rw [this]; exact (hMN'Z.trans ha₃).neg_right
  have hMd : (M : ℤ) ∣ 1 - d₃ := by
    have : 1 - d₃ = -(d₃ - 1) := by ring
    rw [this]; exact (hMN'Z.trans hd₃).neg_right
  have hM00 : (M : ℤ) ∣ P 0 0 - m₃ 0 0 := by
    rw [eP00, ← ha₃def]
    have : (1 + β₂ * (1 - d₃)) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) - a₃
        = (1 - a₃) + β₂ * (1 - d₃) + (β₁ * (1 + β₂ * (1 - d₃)) + β₂) * (1 - a₃) := by ring
    rw [this]
    exact dvd_add (dvd_add hMa (dvd_mul_of_dvd_left hβ₂M _)) (dvd_mul_of_dvd_right hMa _)
  have hM01 : (M : ℤ) ∣ P 0 1 - m₃ 0 1 := by
    rw [eP01]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hβ₁M _) hβ₂M) (hMNZ.trans hb₃)
  have hM10 : (M : ℤ) ∣ P 1 0 - m₃ 1 0 := by
    rw [eP10]
    exact dvd_sub (dvd_add hMd (dvd_mul_of_dvd_right hMa _)) (hMNZ.trans hc₃)
  have hM11 : (M : ℤ) ∣ P 1 1 - m₃ 1 1 := by
    rw [eP11, ← hd₃def]
    have : β₁ * (1 - d₃) + 1 - d₃ = β₁ * (1 - d₃) + (1 - d₃) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hMd _) hMd

  have hcopZ : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hN : ∀ i j, (N : ℤ) ∣ P i j - m₃ i j := by
    intro i j
    rw [hNqM]
    fin_cases i <;> fin_cases j
    · exact hcopZ.mul_dvd hq00 hM00
    · exact hcopZ.mul_dvd hq01 hM01
    · exact hcopZ.mul_dvd hq10 hM10
    · exact hcopZ.mul_dvd hq11 hM11
  have hmem : m₃ * P⁻¹ ∈ Gamma N := mul_inv_mem_Gamma hN
  have := mul_mem (Gamma_le_G hmem) hPG
  rwa [inv_mul_cancel_right] at this

theorem main : Gamma (N / p) ≤ G N p := by
  intro m hm
  obtain ⟨hqM, hNp, hMN', hcop, hpM, hqN, hpq⟩ := setup hp hpN
  by_cases hd : (p : ℤ) ∣ m 1 1
  ·
    have hL : Low (-((N / p : ℕ) : ℤ)) ∈ Gamma (N / p) := Low_mem_Gamma_of_dvd (dvd_neg.mpr dvd_rfl)
    have hm' : Low (-((N / p : ℕ) : ℤ)) * m ∈ Gamma (N / p) := mul_mem hL hm
    obtain ⟨ha, hb, hc, hdd⟩ := (mem_Gamma_iff _ _).mp hm
    have hdet := det_eq m

    have hpN' : ¬ (p : ℤ) ∣ ((N / p : ℕ) : ℤ) := by
      intro h
      have h1 : (p : ℤ) ∣ m 1 1 - 1 := h.trans hdd
      have : (p : ℤ) ∣ 1 := by
        have := dvd_sub hd h1; rwa [sub_sub_cancel] at this
      exact hp.one_lt.ne' (Int.natCast_dvd_natCast.mp (by simpa using this) |> Nat.dvd_one.mp)
    have hpb : ¬ (p : ℤ) ∣ m 0 1 := by
      intro h
      have : (p : ℤ) ∣ 1 := by
        rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_right hd _) (dvd_mul_of_dvd_left h _)
      exact hp.one_lt.ne' (Int.natCast_dvd_natCast.mp (by simpa using this) |> Nat.dvd_one.mp)
    have hd' : ¬ (p : ℤ) ∣ (Low (-((N / p : ℕ) : ℤ)) * m) 1 1 := by
      rw [Low_mul_apply]
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      intro h
      have h2 : (p : ℤ) ∣ -((N / p : ℕ) : ℤ) * m 0 1 := by
        have := dvd_sub h hd; rwa [add_sub_cancel_left] at this
      rw [neg_mul, dvd_neg] at h2
      rcases (Int.Prime.dvd_mul' hp h2) with h3 | h3
      · exact hpN' h3
      · exact hpb h3
    have hmem := mem_G_of_not_dvd hp hpN _ hm' hd'
    have hLG : Low (-((N / p : ℕ) : ℤ)) ∈ G N p :=
      Low_mem_G_of_dvd (dvd_neg.mpr dvd_rfl)
    have := mul_mem (inv_mem hLG) hmem
    rwa [inv_mul_cancel_left] at this
  · exact mem_G_of_not_dvd hp hpN m hm hd

end Main

end GammaGenSol
p2m_reactivate "P2MW.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers.GammaGenSol"

open CongruenceSubgroup in
theorem solution
    (N p : ℕ) [NeZero N] (hp : p.Prime) (hpN : p ∣ N) :
    Gamma (N / p) ≤ (Gamma1 N ⊓ Gamma (N / p ^ N.factorization p)) ⊔
      Subgroup.zpowers (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) :=
  GammaGenSol.main hp hpN

end S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
end P2MW
export P2MW.S_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers (solution)
