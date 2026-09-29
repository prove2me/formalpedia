-- Prove2me | solution 1 for GT.inv_u3
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:51.377965+00:00
-- url     : https://prove2.me/submissions/6f0a96ea-9aec-4605-aa83-34939a9eab74

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_num_mid
import Theorems.Thm_GT_u3_back
import Theorems.Thm_GT_u3_front
import Theorems.Thm_GT_u3_mid

section File_GT_InvU3Num
/-!
# Numerical bookkeeping for the local inverse `U³` theorem

All the scale conditions have the form `θ * M ≤ ε`, where `M` is at most a fixed power of the
huge quantity `H = exp(D³)`, `D = s + J + 1`, `ε` is at least a fixed negative power of `H`, and
`θ ≤ exp(-D⁴) ≤ H^{-2^29}`.
-/

open Finset KM

namespace GT

noncomputable section

/-- `D = s + J + 1`. -/
def u3D (s : ℕ) (η : ℝ) : ℝ := s + u3J η + 1

/-- `H = exp(D³)`. -/
def u3H (s : ℕ) (η : ℝ) : ℝ := Real.exp (u3D s η ^ 3)

lemma master_le {θ M ε H : ℝ} {N a b : ℕ} (hH : 1 ≤ H) (hθ0 : 0 ≤ θ) (hθ : θ ≤ (H ^ N)⁻¹)
    (hM0 : 0 ≤ M) (hM : M ≤ H ^ a) (hε : (H ^ b)⁻¹ ≤ ε) (hab : a + b ≤ N) : θ * M ≤ ε := by
  have hH0 : 0 < H := by linarith
  have key : H ^ a * H ^ b ≤ H ^ N := by rw [← pow_add]; exact pow_le_pow_right₀ hH hab
  calc θ * M ≤ (H ^ N)⁻¹ * H ^ a := mul_le_mul hθ hM hM0 (by positivity)
    _ ≤ (H ^ b)⁻¹ := by
      rw [inv_mul_le_iff₀ (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      exact key
    _ ≤ ε := hε

section basic

variable {s : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
include hη0 hη

lemma u3X_ge : (2 : ℝ) ^ 30 ≤ 1 / η := by
  rw [le_div_iff₀ hη0]; rw [le_div_iff₀ (by positivity)] at hη; linarith

lemma u3J_ge : 1 / η ≤ u3J η := by
  unfold u3J u3EJ
  have h1 : (1 : ℝ) ≤ 1 / η := le_trans (by norm_num) (u3X_ge hη0 hη)
  calc 1 / η = (1 / η) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ h1 (by norm_num)

lemma u3D_ge_J : u3J η + 1 ≤ u3D s η := by
  unfold u3D; have : (0 : ℝ) ≤ s := by positivity
  linarith

lemma u3D_ge : (2 : ℝ) ^ 30 ≤ u3D s η := by
  have := u3X_ge hη0 hη; have := u3J_ge hη0 hη; have := u3D_ge_J (s := s) hη0 hη
  linarith

lemma u3D_pos : 0 < u3D s η := lt_of_lt_of_le (by positivity) (u3D_ge hη0 hη)

lemma u3_log_le : 2 ^ 24 * Real.log (1 / η) ≤ u3D s η := by
  have hX : 0 < 1 / η := by positivity
  have hJ : Real.log (u3J η) = 2 ^ 24 * Real.log (1 / η) := by
    unfold u3J u3EJ; rw [Real.log_pow]; push_cast; ring
  have hJ0 : 0 < u3J η := lt_of_lt_of_le hX (u3J_ge hη0 hη)
  have := Real.log_le_sub_one_of_pos hJ0
  have := u3D_ge_J (s := s) hη0 hη
  linarith

lemma u3_log_nonneg : 0 ≤ Real.log (1 / η) :=
  Real.log_nonneg (le_trans (by norm_num) (u3X_ge hη0 hη))

lemma u3H_ge_one : 1 ≤ u3H s η := by
  unfold u3H; exact Real.one_le_exp (by have := u3D_pos (s := s) hη0 hη; positivity)

lemma u3D_le_H : u3D s η ≤ u3H s η := by
  unfold u3H
  have hD := u3D_ge (s := s) hη0 hη
  have h1 : u3D s η ≤ u3D s η ^ 3 := by
    have h1 : (1 : ℝ) ≤ u3D s η := le_trans (by norm_num) hD
    have h2 : (1 : ℝ) ≤ u3D s η ^ 2 := one_le_pow₀ h1
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ u3D s η)
    calc u3D s η = u3D s η * 1 := (mul_one _).symm
      _ ≤ u3D s η * u3D s η ^ 2 := this
      _ = _ := by ring
  have := Real.add_one_le_exp (u3D s η ^ 3)
  linarith

lemma le_H_of_le_D {x : ℝ} (hx : x ≤ u3D s η) : x ≤ u3H s η := hx.trans (u3D_le_H hη0 hη)

lemma inv_eta_le_H : 1 / η ≤ u3H s η := by
  refine le_H_of_le_D hη0 hη ?_
  have := u3J_ge hη0 hη; have := u3D_ge_J (s := s) hη0 hη; linarith

lemma const_le_H {c : ℝ} (hc : c ≤ 2 ^ 30) : c ≤ u3H s η :=
  le_H_of_le_D hη0 hη (hc.trans (u3D_ge hη0 hη))

lemma eta_pow_ge (k : ℕ) : (u3H s η ^ k)⁻¹ ≤ η ^ k := by
  have h := inv_eta_le_H (s := s) hη0 hη
  rw [← inv_pow]
  apply pow_le_pow_left₀ (by have := u3H_ge_one (s := s) hη0 hη; positivity)
  rw [one_div] at h
  exact (inv_le_comm₀ (by linarith [u3H_ge_one (s := s) hη0 hη]) hη0).2 h

lemma two_pow_sq_le_H {n : ℕ} (hn : (n : ℝ) ≤ u3D s η) : (2 : ℝ) ^ (n ^ 2) ≤ u3H s η := by
  unfold u3H
  have hD := u3D_ge (s := s) hη0 hη
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  calc (2 : ℝ) ^ (n ^ 2) ≤ Real.exp 1 ^ (n ^ 2) := pow_le_pow_left₀ (by norm_num) h2 _
    _ = Real.exp ((n : ℝ) ^ 2) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ Real.exp (u3D s η ^ 3) := by
      apply Real.exp_le_exp.2
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have : (1 : ℝ) ≤ u3D s η := le_trans (by norm_num) hD
      have : (n : ℝ) ^ 2 ≤ u3D s η ^ 2 := pow_le_pow_left₀ hn0 hn 2
      nlinarith

lemma u3θ_le : u3θ s η ≤ (u3H s η ^ (2 ^ 29))⁻¹ := by
  unfold u3θ u3H
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  apply Real.exp_le_exp.2
  have hD := u3D_ge (s := s) hη0 hη
  change -(u3D s η) ^ 4 ≤ -(((2 ^ 29 : ℕ) : ℝ) * u3D s η ^ 3)
  push_cast
  have h3 : 0 ≤ u3D s η ^ 3 := by have := u3D_pos (s := s) hη0 hη; positivity
  have : (2 : ℝ) ^ 29 ≤ u3D s η := le_trans (by norm_num) hD
  nlinarith

end basic

/-! ### The number of filters and the density -/

section filters

variable {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
include hη0 hη

lemma u3m_pow_bounds : 1 / η ≤ 2 ^ (Nat.log 2 ⌊1 / η⌋₊ + 1) ∧
    (2 : ℝ) ^ (Nat.log 2 ⌊1 / η⌋₊ + 1) ≤ 2 * (1 / η) := by
  have hX := u3X_ge hη0 hη
  have hX0 : (0 : ℝ) ≤ 1 / η := by positivity
  set n := ⌊1 / η⌋₊ with hn
  have hn1 : 1 ≤ n := by
    rw [hn]; apply Nat.le_floor; push_cast; linarith [show (1 : ℝ) ≤ 2 ^ 30 by norm_num]
  constructor
  · have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have h2 : (n : ℝ) + 1 ≤ 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast h1
    have h3 := Nat.lt_floor_add_one (1 / η)
    rw [← hn] at h3
    linarith
  · have h1 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast h1
    have h3 : (n : ℝ) ≤ 1 / η := Nat.floor_le hX0
    rw [pow_succ]; linarith

lemma u3m_ge : 1 ≤ u3m η := by unfold u3m; omega

lemma u3m_mL : 16 * u3L ≤ 2 ^ u3m η * (η ^ 8 / 2 ^ 26) := by
  obtain ⟨h1, -⟩ := u3m_pow_bounds hη0 hη
  unfold u3m u3L
  rw [pow_add, pow_mul]
  set N := Nat.log 2 ⌊1 / η⌋₊ + 1
  have h8 : (1 / η) ^ 8 ≤ ((2 : ℝ) ^ N) ^ 8 := pow_le_pow_left₀ (by positivity) h1 8
  have e : (1 / η) ^ 8 * η ^ 8 = 1 := by rw [← mul_pow, one_div, inv_mul_cancel₀ hη0.ne', one_pow]
  have hη8 : 0 < η ^ 8 := by positivity
  have : ((2 : ℝ) ^ 8) ^ N = ((2 : ℝ) ^ N) ^ 8 := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [this]
  calc 16 * (10 : ℝ) ^ 6 ≤ 2 ^ 60 * ((1 / η) ^ 8 * η ^ 8) / 2 ^ 26 := by rw [e]; norm_num
    _ ≤ 2 ^ 60 * (((2 : ℝ) ^ N) ^ 8 * η ^ 8) / 2 ^ 26 := by gcongr
    _ = _ := by ring

lemma u3m_le : (u3m η : ℝ) ≤ 17 * (1 / η) := by
  obtain ⟨-, h2⟩ := u3m_pow_bounds hη0 hη
  have hX := u3X_ge hη0 hη
  have hN : ((Nat.log 2 ⌊1 / η⌋₊ + 1 : ℕ) : ℝ) ≤ 2 ^ (Nat.log 2 ⌊1 / η⌋₊ + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self).le
  unfold u3m
  push_cast at hN ⊢
  have : (68 : ℝ) ≤ 1 / η := le_trans (by norm_num) hX
  linarith

lemma u3c3_ge : η ^ 215 ≤ u3c3 η := by
  obtain ⟨-, h2⟩ := u3m_pow_bounds hη0 hη
  have hX := u3X_ge hη0 hη
  set N := Nat.log 2 ⌊1 / η⌋₊ + 1 with hN
  unfold u3c3 u3m
  rw [← hN]
  -- `(10^-6)^m ≥ (2^-20)^m = (2^m)^-20`
  have h1 : ((1 : ℝ) / 2 ^ 20) ^ (8 * N + 60) ≤ (1 / 10 ^ 6) ^ (8 * N + 60) :=
    pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h2' : (2 : ℝ) ^ (8 * N + 60) ≤ (2 * (1 / η)) ^ 8 * 2 ^ 60 := by
    rw [pow_add, pow_mul']; gcongr
  have h3 : ((1 : ℝ) / 2 ^ 20) ^ (8 * N + 60) = ((2 : ℝ) ^ (8 * N + 60))⁻¹ ^ 20 := by
    rw [one_div, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm]
  have h4 : ((2 * (1 / η)) ^ 8 * 2 ^ 60)⁻¹ ^ 20 ≤ ((2 : ℝ) ^ (8 * N + 60))⁻¹ ^ 20 := by
    gcongr
  have h5a : ((2 * (1 / η)) ^ 8 * 2 ^ 60) = 2 ^ 68 / η ^ 8 := by
    field_simp
  have h5 : ((2 * (1 / η)) ^ 8 * 2 ^ 60)⁻¹ ^ 20 = η ^ 160 / 2 ^ 1360 := by
    rw [h5a, inv_div, div_pow, ← pow_mul, ← pow_mul]
  have hη2 : (1 : ℝ) / 2 ^ 1360 ≥ η ^ 46 := by
    have : η ^ 46 ≤ (1 / 2 ^ 30) ^ 46 := pow_le_pow_left₀ hη0.le hη 46
    calc η ^ 46 ≤ (1 / 2 ^ 30) ^ 46 := this
      _ ≤ 1 / 2 ^ 1360 := by
        rw [div_pow, one_pow, ← pow_mul]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hη3 : (1 : ℝ) / (2 ^ 26 * 4) ≥ η := by
    calc η ≤ 1 / 2 ^ 30 := hη
      _ ≤ _ := by norm_num
  calc η ^ 215 = η ^ 46 * η ^ 160 * η ^ 8 * η := by ring
    _ ≤ (1 / 2 ^ 1360) * η ^ 160 * η ^ 8 * (1 / (2 ^ 26 * 4)) := by gcongr
    _ = η ^ 160 / 2 ^ 1360 * (η ^ 8 / 2 ^ 26) / 4 := by ring
    _ ≤ (1 / 10 ^ 6) ^ (8 * N + 60) * (η ^ 8 / 2 ^ 26) / 4 := by
      gcongr; rw [← h5]; exact h4.trans (h3 ▸ h1)

lemma u3c3_pos : 0 < u3c3 η := by unfold u3c3; positivity

lemma u3c3_le : u3c3 η ≤ η ^ 8 / 2 ^ 28 := by
  unfold u3c3
  have : (1 / 10 ^ 6 : ℝ) ^ u3m η ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have : 0 ≤ η ^ 8 / 2 ^ 26 := by positivity
  calc (1 / 10 ^ 6 : ℝ) ^ u3m η * (η ^ 8 / 2 ^ 26) / 4 ≤ 1 * (η ^ 8 / 2 ^ 26) / 4 := by gcongr
    _ = _ := by ring

lemma u3c3_le' : u3c3 η ≤ 1 / 2 ^ 30 := by
  refine (u3c3_le hη0 hη).trans ?_
  have h8 : η ^ 8 ≤ η := pow_le_of_le_one hη0.le (hη.trans (by norm_num)) (by norm_num)
  calc η ^ 8 / 2 ^ 28 ≤ η / 1 := by gcongr; norm_num
    _ ≤ _ := by rw [div_one]; exact hη

end filters

end

end GT
end File_GT_InvU3Num

section File_GT_InvU3NumA
/-!
# Numerical bookkeeping for the local inverse `U³` theorem: steps one to three
-/

open Finset KM

namespace GT

noncomputable section

section helpers

variable {s : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
include hη0 hη

lemma mulH {x y : ℝ} {a b : ℕ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ u3H s η ^ a)
    (hy : y ≤ u3H s η ^ b) : x * y ≤ u3H s η ^ (a + b) := by
  rw [pow_add]
  exact mul_le_mul hx hy hy0 (by have := u3H_ge_one (s := s) hη0 hη; positivity)

lemma natH {n : ℕ} (hn : (n : ℝ) ≤ u3D s η) : (n : ℝ) ≤ u3H s η ^ 1 := by
  rw [pow_one]; exact le_H_of_le_D hη0 hη hn

lemma constH {c : ℝ} (hc : c ≤ 2 ^ 30) : c ≤ u3H s η ^ 1 := by
  rw [pow_one]; exact const_le_H hη0 hη hc

lemma epsH (k : ℕ) {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 2 ^ 30) :
    (u3H s η ^ (k + 1))⁻¹ ≤ η ^ k / c := by
  refine (eta_pow_ge hη0 hη (k + 1)).trans ?_
  have hX := u3X_ge hη0 hη
  have hηc : η ≤ 1 / c := by
    rw [le_div_iff₀ hc0]
    rw [le_div_iff₀ hη0] at hX
    nlinarith
  rw [pow_succ, le_div_iff₀ hc0]
  have : 0 ≤ η ^ k := by positivity
  calc η ^ k * η * c ≤ η ^ k * (1 / c) * c := by gcongr
    _ = η ^ k := by field_simp

lemma thetaM {θ M ε : ℝ} {a b : ℕ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ u3θ s η) (hM0 : 0 ≤ M)
    (hM : M ≤ u3H s η ^ a) (hε : (u3H s η ^ b)⁻¹ ≤ ε) (hab : a + b ≤ 2 ^ 29) : θ * M ≤ ε :=
  master_le (u3H_ge_one hη0 hη) hθ0 ((hθ.trans (u3θ_le hη0 hη))) hM0 hM hε hab

lemma card_le_D {sc : ℕ} (hsc : sc ≤ s) : (sc : ℝ) ≤ u3D s η := by
  unfold u3D
  have : (sc : ℝ) ≤ s := by exact_mod_cast hsc
  have : 0 ≤ u3J η := le_trans (by positivity) (u3J_ge hη0 hη)
  linarith

lemma theta_le_small {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ u3θ s η) : θ ≤ 1 / 2 ^ 30 := by
  have := thetaM hη0 hη (M := 1) (ε := 1 / 2 ^ 30) (a := 0) (b := 31) hθ0 hθ (by norm_num)
    (by simp) (by
      refine (epsH hη0 hη 30 (c := 1) (by norm_num) (by norm_num)).trans ?_
      rw [div_one]; exact (pow_le_pow_left₀ hη0.le hη 30).trans (by norm_num)) (by norm_num)
  simpa using this

end helpers

set_option maxHeartbeats 4000000 in
/-- The numerical hypotheses of the first three steps. -/
theorem num_front {s sc p : ℕ} (hsc : sc ≤ s) {η θ ρ0 : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
    (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η) (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1)
    (hpl : u3P s η θ ρ0 ≤ p) :
    4 * (θ * ρ0) ≤ ρ0 ∧ 4 * (θ ^ 2 * ρ0) ≤ ρ0 ∧ 4 * (θ ^ 2 * ρ0) ≤ θ * ρ0 ∧
    8 * (θ ^ 3 * ρ0) ≤ θ ^ 2 * ρ0 ∧ θ ^ 4 * ρ0 ≤ θ ^ 3 * ρ0 ∧ θ ^ 2 * ρ0 ≤ 1 ∧
    7200 * (sc : ℝ) * (θ * ρ0) ≤ (η / 4) ^ 2 * ρ0 ∧
    100 * (sc : ℝ) * (θ ^ 2 * ρ0) ≤ η / 2 * ρ0 ∧
    50 * (sc : ℝ) * (θ ^ 2 * ρ0) / (θ * ρ0) ≤ η ^ 2 / 64 ∧
    150 * (sc : ℝ) * (θ ^ 3 * ρ0) / (θ ^ 2 * ρ0) ≤ η ^ 8 / 2 ^ 26 ∧
    2 * (θ ^ 3 * ρ0) ≤ θ ^ 2 * ρ0 ∧
    13 * (sc : ℝ) / ((θ * ρ0) * (η ^ 8 / 2 ^ 25)) * (θ ^ 2 * ρ0) ≤ 1 / 1000 ∧
    13 * (sc : ℝ) / ((θ * ρ0) * (η ^ 8 / 2 ^ 25)) ≤ 1 / (θ ^ 3 * ρ0) ∧
    (10 : ℝ) ^ 60 * (u3m η : ℝ) ^ 10 ≤ p ∧
    50 * (sc : ℝ) * ((θ ^ 3 * ρ0) / 2) / (θ ^ 2 * ρ0) ≤ 1 / (4 * (u3m η : ℝ)) ∧
    (4 * (gM (u3m η) : ℝ)) ^ 3 * (1 / (p * ((θ ^ 4 * ρ0) / 4) ^ sc)) ≤
      (1 / 10 ^ 6) ^ u3m η * (η ^ 8 / 2 ^ 26) / (8 * u3L) := by
  have hθs := theta_le_small hη0 hη hθ0.le hθ
  have hθ1 : θ ≤ 1 / 16 := hθs.trans (by norm_num)
  have hθ1' : θ ≤ 1 := by linarith
  have hsc0 : (0 : ℝ) ≤ sc := by positivity
  have hscH : (sc : ℝ) ≤ u3H s η ^ 1 := natH hη0 hη (card_le_D hη0 hη hsc)
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  have hθ3 : θ ^ 3 ≤ θ ^ 2 := by nlinarith
  have hθ4 : θ ^ 4 ≤ θ ^ 3 := by nlinarith
  have hθ2p : 0 < θ ^ 2 := by positivity
  have hX := u3X_ge hη0 hη
  have hm1 := u3m_ge hη0 hη
  have hm := u3m_le hη0 hη
  -- a generic estimate `θ * (c * sc) ≤ η ^ k / c'`
  have key : ∀ (c c' : ℝ) (k : ℕ), k ≤ 1000 → 0 ≤ c → c ≤ 2 ^ 30 → 0 < c' → c' ≤ 2 ^ 30 →
      θ * (c * sc) ≤ η ^ k / c' := fun c c' k hk hc0 hc hc'0 hc' =>
    thetaM hη0 hη hθ0.le hθ (by positivity) (mulH hη0 hη hc0 hsc0 (constH hη0 hη hc) hscH)
      (epsH hη0 hη k hc'0 hc') (by omega)
  -- the size of `p`
  set NJ := ⌊u3J η⌋₊
  set Y := (4 / (θ ^ u3T η * ρ0)) ^ (4 * (s + NJ + 1)) with hY
  have hTρ : θ ^ u3T η * ρ0 ≤ θ ^ 4 * ρ0 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hθ0.le hθ1' (by unfold u3T; omega)) hρ0.le
  have hTρ0 : 0 < θ ^ u3T η * ρ0 := by positivity
  have hTρ1 : θ ^ u3T η * ρ0 ≤ 1 := by
    have : θ ^ u3T η ≤ 1 := pow_le_one₀ hθ0.le hθ1'
    nlinarith
  have hb1 : 1 ≤ 4 / (θ ^ u3T η * ρ0) := by rw [le_div_iff₀ hTρ0]; linarith
  have hY1 : 1 ≤ Y := one_le_pow₀ hb1
  have hZY : (4 / (θ ^ 4 * ρ0)) ^ sc ≤ Y := by
    have hb : 4 / (θ ^ 4 * ρ0) ≤ 4 / (θ ^ u3T η * ρ0) := by gcongr
    have hb' : 1 ≤ 4 / (θ ^ 4 * ρ0) := by
      rw [le_div_iff₀ (by positivity)]
      have : θ ^ 4 ≤ 1 := pow_le_one₀ hθ0.le hθ1'
      nlinarith
    calc (4 / (θ ^ 4 * ρ0)) ^ sc ≤ (4 / (θ ^ u3T η * ρ0)) ^ sc := by gcongr
      _ ≤ Y := by
        have hsc4 : sc ≤ 4 * (s + NJ + 1) := by omega
        exact pow_le_pow_right₀ hb1 hsc4
  have hpY : Y * (1 / η) ^ (2 ^ 30) ≤ p := hpl
  have hXp : (1 / η) ^ (2 ^ 30) ≤ (p : ℝ) := by
    have : (1 / η) ^ (2 ^ 30) ≤ Y * (1 / η) ^ (2 ^ 30) := le_mul_of_one_le_left (by positivity) hY1
    linarith
  have hXη : (1 / η) * η = 1 := by field_simp
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    mul_le_mul_of_nonneg_right hθ4 hρ0.le, ?_, ?_, ?_, ?_, ?_, by nlinarith, ?_, ?_, ?_, ?_, ?_⟩
  · have : θ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · have h := key 7200 16 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have e : (η / 4) ^ 2 = η ^ 2 / 16 := by ring
    rw [e]; nlinarith
  · have h := key 100 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [pow_one] at h
    have : θ ^ 2 * (100 * sc) ≤ θ * (100 * sc) := by gcongr
    nlinarith
  · have e : 50 * (sc : ℝ) * (θ ^ 2 * ρ0) / (θ * ρ0) = θ * (50 * sc) := by
      field_simp
    rw [e]; exact key 50 64 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have e : 150 * (sc : ℝ) * (θ ^ 3 * ρ0) / (θ ^ 2 * ρ0) = θ * (150 * sc) := by
      field_simp
    rw [e]; exact key 150 (2 ^ 26) 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · have h := key (13 * 2 ^ 25) 1000 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have e : 13 * (sc : ℝ) / ((θ * ρ0) * (η ^ 8 / 2 ^ 25)) * (θ ^ 2 * ρ0) =
        θ * (13 * 2 ^ 25 * sc) / η ^ 8 := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  · have h := key (13 * 2 ^ 25) 1 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    rw [div_one] at h
    have e : 13 * (sc : ℝ) / ((θ * ρ0) * (η ^ 8 / 2 ^ 25)) =
        13 * 2 ^ 25 * sc / (θ * ρ0 * η ^ 8) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2 : θ ^ 2 * (13 * 2 ^ 25 * sc) ≤ θ * (13 * 2 ^ 25 * sc) := by gcongr
    have : θ ^ 2 * (13 * 2 ^ 25 * sc) ≤ η ^ 8 := h2.trans h
    calc 13 * 2 ^ 25 * (sc : ℝ) * (θ ^ 3 * ρ0) = (θ ^ 2 * (13 * 2 ^ 25 * sc)) * (θ * ρ0) := by
          ring
      _ ≤ η ^ 8 * (θ * ρ0) := by gcongr
      _ = 1 * (θ * ρ0 * η ^ 8) := by ring
  · -- `10^60 m^10 ≤ p`
    refine le_trans ?_ hXp
    have hm0 : (0 : ℝ) ≤ u3m η := by positivity
    have h1 : (u3m η : ℝ) ^ 10 ≤ (17 * (1 / η)) ^ 10 := pow_le_pow_left₀ hm0 hm 10
    have hX1 : (1 : ℝ) ≤ 1 / η := le_trans (by norm_num) hX
    have h2 : (10 : ℝ) ^ 60 * 17 ^ 10 ≤ (1 / η) ^ 9 :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hX 9)
    calc (10 : ℝ) ^ 60 * (u3m η : ℝ) ^ 10 ≤ 10 ^ 60 * (17 * (1 / η)) ^ 10 := by gcongr
      _ = (10 ^ 60 * 17 ^ 10) * (1 / η) ^ 10 := by ring
      _ ≤ (1 / η) ^ 9 * (1 / η) ^ 10 := by gcongr
      _ = (1 / η) ^ 19 := by ring
      _ ≤ (1 / η) ^ (2 ^ 30) := pow_le_pow_right₀ hX1 (by norm_num)
  · have e : 50 * (sc : ℝ) * ((θ ^ 3 * ρ0) / 2) / (θ ^ 2 * ρ0) = θ * (25 * sc) := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have hmH : (u3m η : ℝ) ≤ u3H s η ^ 2 := by
      have : 17 * (1 / η) ≤ u3H s η ^ 1 * u3H s η ^ 1 :=
        mul_le_mul (constH hη0 hη (by norm_num)) (by rw [pow_one]; exact inv_eta_le_H hη0 hη)
          (by positivity) (by have := u3H_ge_one (s := s) hη0 hη; positivity)
      rw [← pow_add] at this; linarith
    have h := thetaM hη0 hη (M := 100 * sc * u3m η) (ε := 1) (a := 4) (b := 0) hθ0.le hθ
      (by positivity) (by
        have := mulH hη0 hη (by positivity) (by positivity)
          (mulH hη0 hη (x := 100) (by norm_num) hsc0 (constH hη0 hη (c := 100) (by norm_num))
            hscH) hmH
        simpa using this) (by simp) (by norm_num)
    nlinarith
  · -- the non-generic quadruples
    have hZ : 1 / (p * ((θ ^ 4 * ρ0) / 4) ^ sc) = (4 / (θ ^ 4 * ρ0)) ^ sc / p := by
      rw [div_pow, div_pow]
      field_simp
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hXp
    have hZ' : (4 / (θ ^ 4 * ρ0)) ^ sc / p ≤ η ^ (2 ^ 30) := by
      rw [div_le_iff₀ hp0]
      calc (4 / (θ ^ 4 * ρ0)) ^ sc ≤ Y := hZY
        _ = η ^ (2 ^ 30) * (Y * (1 / η) ^ (2 ^ 30)) := by
          rw [mul_comm Y, ← mul_assoc, ← mul_pow, mul_comm η, hXη, one_pow, one_mul]
        _ ≤ η ^ (2 ^ 30) * p := by gcongr
    have hgM : (4 * (gM (u3m η) : ℝ)) ^ 3 ≤ (1 / η) ^ 12 := by
      have egM : (gM (u3m η) : ℝ) = 2 * 10 ^ 12 * (u3m η : ℝ) ^ 2 := by
        unfold gM; push_cast; ring
      rw [egM]
      have hm0 : (0 : ℝ) ≤ u3m η := by positivity
      have h1 : (u3m η : ℝ) ^ 2 ≤ (17 * (1 / η)) ^ 2 := pow_le_pow_left₀ hm0 hm 2
      have h2 : (4 * (2 * 10 ^ 12 * (u3m η : ℝ) ^ 2)) ≤ (1 / η) ^ 4 := by
        have : (8 * 10 ^ 12 * 17 ^ 2 : ℝ) ≤ (1 / η) ^ 2 :=
          le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hX 2)
        nlinarith
      calc (4 * (2 * 10 ^ 12 * (u3m η : ℝ) ^ 2)) ^ 3 ≤ ((1 / η) ^ 4) ^ 3 :=
            pow_le_pow_left₀ (by positivity) h2 3
        _ = _ := by ring
    have hc3 := u3c3_ge hη0 hη
    unfold u3c3 at hc3
    rw [hZ]
    calc (4 * (gM (u3m η) : ℝ)) ^ 3 * ((4 / (θ ^ 4 * ρ0)) ^ sc / p) ≤
          (1 / η) ^ 12 * η ^ (2 ^ 30) := by gcongr
      _ = η ^ 216 * η ^ (2 ^ 30 - 228) * ((1 / η) * η) ^ 12 := by
          have e : η ^ (2 ^ 30) = η ^ 216 * η ^ (2 ^ 30 - 228) * η ^ 12 := by
            rw [← pow_add, ← pow_add]; norm_num
          rw [e]; ring
      _ ≤ η ^ 216 * 1 * 1 := by
          rw [hXη, one_pow]; gcongr; exact pow_le_one₀ hη0.le (by linarith)
      _ = η ^ 215 * η := by ring
      _ ≤ (1 / 10 ^ 6) ^ u3m η * (η ^ 8 / 2 ^ 26) / 4 * (1 / (2 * 10 ^ 6)) := by
          gcongr; linarith [show (1 : ℝ) / 2 ^ 30 ≤ 1 / (2 * 10 ^ 6) by norm_num]
      _ = _ := by unfold u3L; ring

end

end GT
end File_GT_InvU3NumA

section File_GT_InvU3NumC
/-!
# Numerical bookkeeping for the local inverse `U³` theorem: steps seven to nine
-/

open Finset KM

namespace GT

noncomputable section

section qb

variable {s : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
include hη0 hη

lemma inv_eta_pow_le_exp (k : ℕ) : (1 / η) ^ k = Real.exp (k * Real.log (1 / η)) := by
  rw [Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- The bound on the dilation of the eighth step. -/
lemma pow_sq_le_exp {x : ℝ} (hx1 : 1 ≤ x) (hx : x ≤ (1 / η) ^ 1737) {d : ℕ}
    (hd : (d : ℝ) ≤ u3D s η) : x ^ (d ^ 2) ≤ Real.exp (u3D s η ^ 3 / 2) := by
  have hL0 := u3_log_nonneg hη0 hη
  have hL := u3_log_le (s := s) hη0 hη
  have hD := u3D_ge (s := s) hη0 hη
  have hD0 : 0 ≤ u3D s η := by linarith [show (0 : ℝ) ≤ 2 ^ 30 by positivity]
  calc x ^ (d ^ 2) ≤ ((1 / η) ^ 1737) ^ (d ^ 2) := pow_le_pow_left₀ (by linarith) hx _
    _ = Real.exp (((1737 * d ^ 2 : ℕ) : ℝ) * Real.log (1 / η)) := by
      rw [← pow_mul, inv_eta_pow_le_exp hη0 hη]
    _ ≤ Real.exp (u3D s η ^ 3 / 2) := by
      apply Real.exp_le_exp.2
      push_cast
      have hd2 : (d : ℝ) ^ 2 ≤ u3D s η ^ 2 := pow_le_pow_left₀ (by positivity) hd 2
      have h1 : Real.log (1 / η) ≤ u3D s η / 2 ^ 24 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      calc 1737 * (d : ℝ) ^ 2 * Real.log (1 / η) ≤ 1737 * u3D s η ^ 2 * (u3D s η / 2 ^ 24) := by
            gcongr
        _ ≤ u3D s η ^ 3 / 2 := by
            have : 0 ≤ u3D s η ^ 3 := by positivity
            nlinarith

lemma exp_half_le_H : Real.exp (u3D s η ^ 3 / 2) ≤ u3H s η ^ 1 := by
  rw [pow_one]; unfold u3H
  apply Real.exp_le_exp.2
  have : 0 ≤ u3D s η ^ 3 := by have := u3D_pos (s := s) hη0 hη; positivity
  linarith

lemma two_exp_half_le_H : 2 * Real.exp (u3D s η ^ 3 / 2) ≤ u3H s η := by
  unfold u3H
  have hD := u3D_ge (s := s) hη0 hη
  have h3 : (2 : ℝ) ≤ u3D s η ^ 3 / 2 := by
    have h1 : (1 : ℝ) ≤ u3D s η := le_trans (by norm_num) hD
    have h2 : (1 : ℝ) ≤ u3D s η ^ 2 := one_le_pow₀ h1
    have : u3D s η * 1 ≤ u3D s η * u3D s η ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    have e : u3D s η * u3D s η ^ 2 = u3D s η ^ 3 := by ring
    linarith [show (4 : ℝ) ≤ 2 ^ 30 by norm_num]
  have h2 : (2 : ℝ) ≤ Real.exp (u3D s η ^ 3 / 2) := by
    have := Real.add_one_le_exp (u3D s η ^ 3 / 2); linarith
  calc 2 * Real.exp (u3D s η ^ 3 / 2) ≤ Real.exp (u3D s η ^ 3 / 2) * Real.exp (u3D s η ^ 3 / 2) := by
        gcongr
    _ = Real.exp (u3D s η ^ 3) := by rw [← Real.exp_add]; ring_nf

end qb

set_option maxHeartbeats 8000000 in
/-- The numerical hypotheses of steps seven to nine, and the final bounds. -/
theorem num_back {p : ℕ} [NeZero p] {S T : Finset (ZMod p)} {s : ℕ} {η θ ρ0 : ℝ}
    (hSs : S.card ≤ s) (hTs : T.card ≤ s + ⌊u3J η⌋₊) (hT1 : 1 ≤ T.card)
    (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30) (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η) (hρ0 : 0 < ρ0)
    (hρ01 : ρ0 ≤ 1)
    {r r' r3 ρA ρ4 ρ5 ρ6 ρ9 ρ10 c0 B σ0 : ℝ}
    (hr : r = θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) (hr' : r' = θ * r) (hr3 : r3 = θ * r')
    (hρA : ρA = θ * r3) (hρ4 : ρ4 = θ * ρA) (hρ5 : ρ5 = θ * ρ4) (hρ6 : ρ6 = θ * ρ5)
    (hρ9 : ρ9 = θ * ρ6) (hρ10 : ρ10 = θ ^ 3 * ρ9) (hc0 : c0 = u3c3 η * η / 288)
    (hB : B = 24 * (1 / (θ ^ 3 * ρ0))) (hσ0 : σ0 = 2 * (θ ^ 2 * ρ0) + r') :
    0 < c0 ∧
    4 * ρ5 ≤ ρ4 ∧ 4 * ρ6 ≤ r' ∧ 4 * ρ4 ≤ ρ0 ∧ r' + ρ6 ≤ r / 2 ∧
    err7 S T B ρ0 r' r3 ρ4 ρ5 ρ6 ≤ c0 / 2 ∧
    4 * (2 ^ (T.card ^ 2) * T.card) * ρA ≤ r3 ∧
    (2 * T.card + 1) * (2 ^ (T.card ^ 2) * T.card) * ρA + r3 ≤ r / 2 ∧
    2 * T.card * (2 ^ (T.card ^ 2) * T.card) * ρA < 1 ∧
    4 * B * ρA < 1 ∧
    8 * ρ6 ≤ ρ5 ∧ 4 * ρ5 ≤ ρA ∧ 100 * T.card * ρ6 / ρ5 ≤ (c0 / 2) ^ 2 / 2 ∧
    ρ9 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6 ∧ ρ10 ≤ lqR T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6 ∧
    4 * ((2 * qbar T c0 ρ5 ρ6) * ρ10) ≤ ρ5 ∧ 4 * ((2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ6 ∧
    ρ6 + ρ5 + (2 * qbar T c0 ρ5 ρ6) * (ρ9 + ρ10) ≤ ρA ∧
    err9 T c0 ρ5 ρ6 ρ9 ρ10 ≤ c0 / 4 ∧
    4 * ρ10 ≤ ρ9 ∧ 7200 * T.card * ρ10 ≤ ((c0 / 4) ^ 2 / 2) ^ 2 * ρ9 ∧
    2 * (ρ9 + ρ10) ≤ ρA ∧ 16 * ρ10 ≤ ρA ∧
    4 * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) ≤ ρ0 ∧
    50 * S.card * (σ0 + r' + ρ5 + ρ6 + (2 * qbar T c0 ρ5 ρ6) * ρ9) / ρ0 ≤
      ((c0 / 4) ^ 2) ^ 2 / 16 ∧
    2 * qbar T c0 ρ5 ρ6 ≤ u3k s η ∧ u3κ η ≤ c0 ^ 4 / 4096 := by
  have hθs := theta_le_small hη0 hη hθ0.le hθ
  have hθ16 : θ ≤ 1 / 16 := hθs.trans (by norm_num)
  have hθ1 : θ ≤ 1 := by linarith
  set H := u3H s η with hH
  have hH1 : 1 ≤ H := u3H_ge_one hη0 hη
  have hH0 : 0 < H := by linarith
  set NJ := ⌊u3J η⌋₊ with hNJ
  -- scales
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrρ : r ≤ ρ0 := by
    have : θ ^ (20 * NJ + 90) ≤ 1 := pow_le_one₀ hθ0.le hθ1
    rw [hr]; exact mul_le_of_le_one_left hρ0.le this
  have hr'0 : 0 < r' := by rw [hr']; positivity
  have hr30 : 0 < r3 := by rw [hr3]; positivity
  have hρA0 : 0 < ρA := by rw [hρA]; positivity
  have hρ40 : 0 < ρ4 := by rw [hρ4]; positivity
  have hρ50 : 0 < ρ5 := by rw [hρ5]; positivity
  have hρ60 : 0 < ρ6 := by rw [hρ6]; positivity
  have hρ90 : 0 < ρ9 := by rw [hρ9]; positivity
  have hρ100 : 0 < ρ10 := by rw [hρ10]; positivity
  have hr'le : r' ≤ θ * ρ0 := by rw [hr']; exact mul_le_mul_of_nonneg_left hrρ hθ0.le
  have hr3le : r3 ≤ θ * r' := hr3.le
  have hr3r : r3 ≤ r' := by rw [hr3]; exact mul_le_of_le_one_left hr'0.le hθ1
  have hρAr : ρA ≤ r3 := by rw [hρA]; exact mul_le_of_le_one_left hr30.le hθ1
  have hρ4r : ρ4 ≤ ρA := by rw [hρ4]; exact mul_le_of_le_one_left hρA0.le hθ1
  have hρ5r : ρ5 ≤ ρ4 := by rw [hρ5]; exact mul_le_of_le_one_left hρ40.le hθ1
  have hρ6r : ρ6 ≤ ρ5 := by rw [hρ6]; exact mul_le_of_le_one_left hρ50.le hθ1
  have hρ9r : ρ9 ≤ ρ6 := by rw [hρ9]; exact mul_le_of_le_one_left hρ60.le hθ1
  have hθ3 : θ ^ 3 ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by norm_num)
  have hρ10r : ρ10 ≤ θ * ρ9 := by rw [hρ10]; exact mul_le_mul_of_nonneg_right hθ3 hρ90.le
  have hr'r : r' ≤ θ * r := hr'.le
  have hρ0r : r ≤ 1 := hrρ.trans hρ01
  -- `c0`
  have hc3 := u3c3_ge hη0 hη
  have hc3le := u3c3_le' hη0 hη
  have hc0e : η ^ 217 ≤ c0 := by
    rw [hc0]
    have : η / 288 ≥ η ^ 2 := by
      have : η ≤ 1 / 288 := hη.trans (by norm_num)
      nlinarith only [this, hη0]
    calc η ^ 217 = η ^ 215 * η ^ 2 := by ring
      _ ≤ u3c3 η * (η / 288) := mul_le_mul hc3 this (by positivity) (u3c3_pos hη0 hη).le
      _ = _ := by ring
  have hc00 : 0 < c0 := lt_of_lt_of_le (by positivity) hc0e
  have hc0le : c0 ≤ 1 / 2 ^ 30 := by
    rw [hc0]
    have : η / 288 ≤ 1 := by linarith [show η ≤ 1 by linarith [show (1 : ℝ) / 2 ^ 30 ≤ 1 by norm_num]]
    calc u3c3 η * η / 288 = u3c3 η * (η / 288) := by ring
      _ ≤ u3c3 η * 1 := mul_le_mul_of_nonneg_left this (u3c3_pos hη0 hη).le
      _ ≤ _ := by rw [mul_one]; exact hc3le
  have hc01 : c0 ≤ 1 := hc0le.trans (by norm_num)
  have hc0pow : ∀ k : ℕ, η ^ (217 * k) ≤ c0 ^ k := fun k => by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hc0e k
  -- `(H^(217k+1))⁻¹ ≤ c0^k / c`
  have epsc : ∀ (k : ℕ) (c : ℝ), 0 < c → c ≤ 2 ^ 30 → (H ^ (217 * k + 1))⁻¹ ≤ c0 ^ k / c :=
    fun k c hc0 hc => (epsH hη0 hη (217 * k) hc0 hc).trans (by gcongr; exact hc0pow k)
  -- the cardinalities
  set dR : ℝ := (T.card : ℝ) with hdR
  have hdR1 : (1 : ℝ) ≤ dR := by rw [hdR]; exact_mod_cast hT1
  have hdD : dR ≤ u3D s η := by
    have h1 : (T.card : ℝ) ≤ s + NJ := by exact_mod_cast hTs
    have h2 : (NJ : ℝ) ≤ u3J η := Nat.floor_le (le_trans (by positivity) (u3J_ge hη0 hη))
    rw [hdR]; unfold u3D; linarith
  have hdH : dR ≤ H ^ 1 := natH hη0 hη hdD
  have hscH : (S.card : ℝ) ≤ H ^ 1 :=
    natH hη0 hη (card_le_D hη0 hη hSs)
  set Cb : ℝ := 2 ^ (T.card ^ 2) * T.card with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hCbp : 0 < Cb := by
    rw [hCb]; have : (0 : ℝ) < T.card := by exact_mod_cast hT1
    positivity
  have hCbH : Cb ≤ H ^ 2 := by
    have := mulH hη0 hη (x := 2 ^ (T.card ^ 2)) (y := dR) (by positivity) (by positivity)
      (by rw [pow_one]; exact two_pow_sq_le_H hη0 hη hdD) hdH
    simpa using this
  have hcH : ∀ c : ℝ, c ≤ 2 ^ 30 → c ≤ H ^ 1 := fun c hc => constH hη0 hη hc
  -- the key smallness
  have key : ∀ {M ε : ℝ} {a b : ℕ}, 0 ≤ M → M ≤ H ^ a → (H ^ b)⁻¹ ≤ ε → a + b ≤ 2 ^ 29 →
      θ * M ≤ ε := fun hM0 hM hε hab => thetaM hη0 hη hθ0.le hθ hM0 hM hε hab
  -- `δ`
  have hT1' : 100 * dR * θ ≤ c0 ^ 2 / 8 := by
    have := key (M := 100 * dR) (a := 2) (b := 217 * 2 + 1) (by positivity)
      (by simpa using mulH hη0 hη (by norm_num) (by positivity) (hcH 100 (by norm_num)) hdH)
      (epsc 2 8 (by norm_num) (by norm_num)) (by norm_num)
    linarith
  set δ := del8 T c0 ρ5 ρ6 with hδdef
  have hρ65 : ρ6 / ρ5 = θ := by rw [hρ6]; field_simp
  have hδe : δ = (c0 / 2) ^ 2 - 100 * dR * θ := by
    rw [hδdef]; unfold del8; rw [mul_div_assoc, hρ65]
  have hδlo : c0 ^ 2 / 8 ≤ δ := by rw [hδe]; linarith only [hT1', show (c0 / 2) ^ 2 = c0 ^ 2 / 4 by ring]
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδlo
  have hδ1 : δ ≤ 1 := by
    rw [hδe]; have : 0 ≤ 100 * dR * θ := by positivity
    have : (c0 / 2) ^ 2 ≤ 1 := by nlinarith only [hc00, hc01]
    linarith
  have hδinv : 1 / δ ≤ H ^ 435 := by
    have h1 : (H ^ 435)⁻¹ ≤ δ := (epsc 2 8 (by norm_num) (by norm_num)).trans hδlo
    rw [one_div]
    have := (inv_le_comm₀ (by positivity) hδ0).1 h1
    exact this
  -- `Q̄`
  set Q := qbar T c0 ρ5 ρ6 with hQdef
  have hbase1 : 1 ≤ 32 / δ ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    have : δ ^ 4 ≤ 1 := pow_le_one₀ hδ0.le hδ1
    linarith
  have hbase2 : 32 / δ ^ 4 ≤ (1 / η) ^ 1737 := by
    have h1 : 32 / δ ^ 4 ≤ 131072 / c0 ^ 8 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (c0 ^ 2 / 8) ^ 4 ≤ δ ^ 4 := pow_le_pow_left₀ (by positivity) hδlo 4
      linarith only [this, show (c0 ^ 2 / 8) ^ 4 = c0 ^ 8 / 4096 by ring]
    have h2 : 131072 / c0 ^ 8 ≤ 131072 * (1 / η) ^ 1736 := by
      rw [div_le_iff₀ (by positivity)]
      have h3 := hc0pow 8
      have e : (1 / η) ^ 1736 * η ^ (217 * 8) = 1 := by
        rw [show 217 * 8 = 1736 by norm_num, ← mul_pow, one_div, inv_mul_cancel₀ hη0.ne', one_pow]
      calc (131072 : ℝ) = 131072 * ((1 / η) ^ 1736 * η ^ (217 * 8)) := by rw [e, mul_one]
        _ ≤ 131072 * ((1 / η) ^ 1736 * c0 ^ 8) := by gcongr
        _ = _ := by ring
    have h4 : (131072 : ℝ) * (1 / η) ^ 1736 ≤ (1 / η) ^ 1737 := by
      rw [show (1 / η) ^ 1737 = (1 / η) * (1 / η) ^ 1736 by ring]
      exact mul_le_mul_of_nonneg_right (le_trans (by norm_num : (131072 : ℝ) ≤ 2 ^ 30) (u3X_ge hη0 hη)) (by positivity)
    linarith
  have hQexp : Q ≤ Real.exp (u3D s η ^ 3 / 2) := by
    rw [hQdef]; unfold qbar; rw [← hδdef]
    exact pow_sq_le_exp hη0 hη hbase1 hbase2 hdD
  have hQ1 : 1 ≤ Q := by rw [hQdef]; unfold qbar; rw [← hδdef]; exact one_le_pow₀ hbase1
  have hQH : Q ≤ H ^ 1 := hQexp.trans (exp_half_le_H hη0 hη)
  have h2QH : 2 * Q ≤ H := by
    have := two_exp_half_le_H (s := s) hη0 hη
    linarith
  -- more `H`-bounds
  have powH : ∀ {x : ℝ} {a : ℕ} (n : ℕ), 0 ≤ x → x ≤ H ^ a → x ^ n ≤ H ^ (a * n) :=
    fun n hx0 hx => by rw [pow_mul]; exact pow_le_pow_left₀ hx0 hx n
  have mH : ∀ {x y : ℝ} {a b : ℕ}, 0 ≤ x → 0 ≤ y → x ≤ H ^ a → y ≤ H ^ b → x * y ≤ H ^ (a + b) :=
    fun hx0 hy0 hx hy => mulH hη0 hη hx0 hy0 hx hy
  have hε4 : (H ^ 1)⁻¹ ≤ 1 / 4 := by
    simpa using epsH hη0 hη 0 (c := 4) (by norm_num) (by norm_num)
  have hkH : u3k s η = H := rfl
  clear_value H NJ dR Cb δ Q
  generalize hsR : ((S.card : ℕ) : ℝ) = sR at hscH ⊢
  have hsR0 : 0 ≤ sR := hsR ▸ Nat.cast_nonneg _
  have hδ4inv : 1 / δ ^ 4 ≤ H ^ (435 * 4) := by
    rw [one_div, ← inv_pow]; rw [one_div] at hδinv; exact powH 4 (by positivity) hδinv
  have hQ0 : 0 ≤ Q := by linarith
  -- smallness facts
  have SCb : θ * (16 * dR * Cb) ≤ 1 / 4 := by
    have hM : 16 * dR * Cb ≤ H ^ 4 := by
      have := mH (by positivity) hCb0 (mH (by norm_num) (by positivity) (hcH 16 (by norm_num)) hdH)
        hCbH
      simpa using this
    have hε : (H ^ 1)⁻¹ ≤ 1 / 4 := hε4
    exact key (by positivity) hM hε (by norm_num)
  have SQ : θ * (16 * Q) ≤ 1 / 4 := by
    have hM : 16 * Q ≤ H ^ 2 := by
      simpa using mH (by norm_num) hQ0 (hcH 16 (by norm_num)) hQH
    have hε : (H ^ 1)⁻¹ ≤ 1 / 4 := hε4
    exact key (by positivity) hM hε (by norm_num)
  -- algebraic identities
  have hρ5e : ρ5 = θ ^ 5 * r := by rw [hρ5, hρ4, hρA, hr3, hr']; ring
  have hρ6e : ρ6 = θ ^ 6 * r := by rw [hρ6, hρ5e]; ring
  have hρAe : ρA = θ ^ 3 * r := by rw [hρA, hr3, hr']; ring
  have hρ4e : ρ4 = θ ^ 4 * r := by rw [hρ4, hρAe]; ring
  have hBρ5 : B * ρ5 = 24 * θ ^ 2 * (r / ρ0) := by rw [hB, hρ5e]; field_simp
  have hBρA : B * ρA = 24 * (r / ρ0) := by rw [hB, hρAe]; field_simp
  have hrr0 : r / ρ0 ≤ 1 := by rw [div_le_one hρ0]; exact hrρ
  have hrr00 : 0 ≤ r / ρ0 := by positivity
  have hθ2 : θ ^ 2 ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by norm_num)
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hr'ρ : r' ≤ r / 16 := by rw [hr']; nlinarith only [hθ16, hr0]
  have hθθ : θ * θ ≤ 1 / 256 := by nlinarith only [hθ16, hθ0]
  have hρ5A : ρ5 ≤ ρA / 16 := by rw [hρ5, hρ4]; nlinarith only [hθθ, hρA0]
  have hQθ : 8 * Q * θ ≤ 1 / 8 := by nlinarith only [SQ]
  -- the radius of the eighth step
  have hδ4H : (H ^ 1740)⁻¹ ≤ δ ^ 4 := by
    have h := hδ4inv
    rw [one_div] at h
    exact (inv_le_comm₀ (by positivity) (by positivity)).2 h
  have hW : 65536 / (δ ^ 4) ^ 3 + 1 ≤ H ^ 5222 := by
    have h1 : 1 / (δ ^ 4) ^ 3 ≤ H ^ (1740 * 3) := by
      rw [one_div, ← inv_pow]; rw [one_div] at hδ4inv; exact powH 3 (by positivity) hδ4inv
    have h2 : 65536 / (δ ^ 4) ^ 3 ≤ H ^ (1 + 1740 * 3) := by
      rw [div_eq_mul_one_div]
      exact mH (by norm_num) (by positivity) (hcH 65536 (by norm_num)) h1
    have h3 : (1 : ℝ) ≤ H ^ (1 + 1740 * 3) := one_le_pow₀ hH1
    have h4 : 2 * H ^ (1 + 1740 * 3) ≤ H ^ 5222 := by
      have h2H : (2 : ℝ) ≤ H := by simpa using hcH 2 (by norm_num)
      calc 2 * H ^ (1 + 1740 * 3) ≤ H * H ^ (1 + 1740 * 3) :=
            mul_le_mul_of_nonneg_right h2H (by positivity)
        _ = H ^ 5222 := by ring
    calc 65536 / (δ ^ 4) ^ 3 + 1 ≤ H ^ (1 + 1740 * 3) + H ^ (1 + 1740 * 3) := add_le_add h2 h3
      _ = 2 * H ^ (1 + 1740 * 3) := by ring
      _ ≤ _ := h4
  have S13 : θ * (200 * dR * Cb * (65536 / (δ ^ 4) ^ 3 + 1)) ≤ δ ^ 4 := by
    have hM : 200 * dR * Cb * (65536 / (δ ^ 4) ^ 3 + 1) ≤ H ^ (1 + 1 + 2 + 5222) :=
      mH (by positivity) (by positivity)
        (mH (by positivity) hCb0 (mH (by norm_num) (by positivity) (hcH 200 (by norm_num)) hdH)
          hCbH) hW
    exact key (by positivity) hM hδ4H (by norm_num)
  have hlqR : θ * ρ6 ≤ lqR T.card (δ ^ 4) ρ6 := by
    unfold lqR lqτ
    rw [← hCb, ← hdR, div_div, le_div_iff₀ (by positivity)]
    have : θ * (200 * dR * Cb * (65536 / (δ ^ 4) ^ 3 + 1)) * ρ6 ≤ δ ^ 4 * ρ6 :=
      mul_le_mul_of_nonneg_right S13 hρ60.le
    calc θ * ρ6 * (200 * dR * (Cb * (65536 / (δ ^ 4) ^ 3 + 1))) =
        θ * (200 * dR * Cb * (65536 / (δ ^ 4) ^ 3 + 1)) * ρ6 := by ring
      _ ≤ δ ^ 4 * ρ6 := this
  refine ⟨hc00, by rw [hρ5]; nlinarith only [hθ16, hρ40], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by rw [hρ6]; nlinarith only [hθ16, hρ50], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hρ10]; nlinarith only [hθ16, hρ90, hθ3], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `4 ρ6 ≤ r'`
    have : 4 * ρ6 ≤ ρ5 := by rw [hρ6]; nlinarith only [hθ16, hρ50]
    linarith
  · have : 4 * ρ4 ≤ ρA := by rw [hρ4]; nlinarith only [hθ16, hρA0]
    linarith
  · linarith
  · -- the error of the seventh step
    unfold err7
    rw [← hCb, ← hdR, hsR]
    have t1 : 50 * dR * ρ6 / r' ≤ θ * (50 * dR) := by
      rw [div_le_iff₀ hr'0]
      have : ρ6 ≤ θ * r' := by rw [hρ6]; nlinarith only [hθ0, hρ5r, hρ4r, hρAr, hr3r]
      have h50 : 0 ≤ 50 * dR := by positivity
      nlinarith only [this, h50]
    have t2 : 2 * (50 * dR * ρ5 / ρ4) = θ * (100 * dR) := by rw [hρ5]; field_simp; ring
    have t3 : 50 * sR * ρ4 / ρ0 ≤ θ * (50 * sR) := by
      rw [div_le_iff₀ hρ0]
      have : ρ4 ≤ θ * ρ0 := by
        rw [hρ4e]
        have : θ ^ 4 ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by norm_num)
        exact mul_le_mul this hrρ hr0.le hθ0.le
      have h50 : (0 : ℝ) ≤ 50 * sR := by positivity
      nlinarith only [this, h50]
    have hBρ5' : B * ρ5 ≤ θ * 24 := by
      rw [hBρ5]
      have : θ ^ 2 * (r / ρ0) ≤ θ := by nlinarith only [hθ2, hrr0, hrr00, hθ0]
      nlinarith only [this]
    have hBρ50 : 0 ≤ B * ρ5 := by rw [hBρ5]; positivity
    have t4 : 2 * (2 * Real.pi * (B * ρ5)) ≤ θ * 400 := by
      nlinarith only [hBρ5', hBρ50, hpi, hpi0, hθ0]
    have t5 : 2 * (2 * Real.pi * (B * ρ5 * (50 * dR * dR * Cb * ρ6 / r3 + 1))) ≤
        θ * (400 * (50 * dR * dR * Cb + 1)) := by
      have hρ63 : ρ6 / r3 ≤ 1 := by rw [div_le_one hr30]; linarith
      have hK0 : 0 ≤ 50 * dR * dR * Cb := by positivity
      have h1 : 50 * dR * dR * Cb * ρ6 / r3 ≤ 50 * dR * dR * Cb := by
        rw [mul_div_assoc]
        exact mul_le_of_le_one_right hK0 hρ63
      have h2 : 0 ≤ 50 * dR * dR * Cb * ρ6 / r3 := by positivity
      have h3 : B * ρ5 * (50 * dR * dR * Cb * ρ6 / r3 + 1) ≤ θ * 24 * (50 * dR * dR * Cb + 1) :=
        mul_le_mul hBρ5' (by linarith) (by linarith) (by positivity)
      have h4 : 0 ≤ B * ρ5 * (50 * dR * dR * Cb * ρ6 / r3 + 1) := by positivity
      nlinarith only [h3, h4, hpi, hpi0, hθ0, hK0]
    have hM : 150 * dR + 50 * sR + 400 + 400 * (50 * dR * dR * Cb + 1) ≤ H ^ 5 := by
      have e1 : dR * dR * Cb ≤ H ^ 4 := by
        have := mH (by positivity) hCb0 (mH (by positivity) (by positivity) hdH hdH) hCbH
        simpa using this
      have h1 : H ≤ H ^ 4 := by simpa using pow_le_pow_right₀ hH1 (show 1 ≤ 4 by norm_num)
      have hc : (10 ^ 6 : ℝ) ≤ H := by simpa using hcH (10 ^ 6) (by norm_num)
      have hdH' : dR ≤ H := by simpa using hdH
      have hscH' : sR ≤ H := by simpa using hscH
      have h6 : 10 ^ 6 * H ^ 4 ≤ H ^ 5 := by
        rw [show H ^ 5 = H * H ^ 4 by ring]
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      have hH4 : 1 ≤ H ^ 4 := one_le_pow₀ hH1
      linarith
    have S7 := key (M := 150 * dR + 50 * sR + 400 + 400 * (50 * dR * dR * Cb + 1))
      (a := 5) (b := 217 * 1 + 1) (by positivity) hM (epsc 1 2 (by norm_num) (by norm_num))
      (by norm_num)
    rw [pow_one] at S7
    have e : θ * (150 * dR + 50 * sR + 400 + 400 * (50 * dR * dR * Cb + 1)) =
      θ * (50 * dR) + θ * (100 * dR) + θ * (50 * sR) + θ * 400 +
        θ * (400 * (50 * dR * dR * Cb + 1)) := by ring
    linarith
  · -- `4 Cb ρA ≤ r3`
    rw [hρA]
    have : 4 * Cb * θ ≤ 1 := by nlinarith only [SCb, hdR1, hCb0, hθ0]
    nlinarith only [this, hr30]
  · rw [hρA]
    have h1 : (2 * dR + 1) * Cb * θ ≤ 1 := by nlinarith only [SCb, hdR1, hCb0, hθ0]
    have h2 : (2 * dR + 1) * Cb * (θ * r3) ≤ r3 := by nlinarith only [h1, hr30]
    have h3 : r3 ≤ r / 16 := by linarith
    linarith
  · have h1 : 2 * dR * Cb * θ ≤ 1 / 2 := by nlinarith only [SCb, hdR1, hCb0, hθ0]
    have h2 : ρA ≤ θ := by
      rw [hρAe]
      have : θ ^ 3 * r ≤ θ * 1 := mul_le_mul hθ3 hρ0r hr0.le hθ0.le
      linarith
    have h3 : 0 ≤ 2 * dR * Cb := by positivity
    have : 2 * dR * Cb * ρA ≤ 2 * dR * Cb * θ := mul_le_mul_of_nonneg_left h2 h3
    linarith
  · -- `4 B ρA < 1`
    have e : 4 * B * ρA = 96 * (r / ρ0) := by rw [mul_assoc, hBρA]; ring
    rw [e]
    have : r / ρ0 ≤ θ := by
      rw [div_le_iff₀ hρ0, hr]
      have : θ ^ (20 * NJ + 90) ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by omega)
      exact mul_le_mul_of_nonneg_right this hρ0.le
    linarith
  · have : 4 * ρ5 ≤ ρ4 := by rw [hρ5]; nlinarith only [hθ16, hρ40]
    linarith
  · -- `hδ`
    rw [mul_div_assoc, hρ65]
    have e : (c0 / 2) ^ 2 / 2 = c0 ^ 2 / 8 := by ring
    rw [e]; linarith
  · rw [hρ9]; exact hlqR
  · calc ρ10 ≤ θ * ρ9 := hρ10r
      _ ≤ ρ9 := by nlinarith only [hθ1, hρ90]
      _ ≤ _ := by rw [hρ9]; exact hlqR
  · -- `4 (2Q ρ10) ≤ ρ5`
    have h1 : ρ10 ≤ θ * ρ5 := by
      calc ρ10 ≤ θ * ρ9 := hρ10r
        _ ≤ θ * ρ5 := mul_le_mul_of_nonneg_left (hρ9r.trans hρ6r) hθ0.le
    nlinarith only [h1, hQθ, hQ0, hρ50]
  · rw [hρ9]
    nlinarith only [hQθ, hQ0, hρ60]
  · have h1 := hρ5A
    have h2 : ρ9 + ρ10 ≤ 2 * (θ * ρ6) := by
      have : ρ10 ≤ θ * ρ6 := by
        calc ρ10 ≤ θ * ρ9 := hρ10r
          _ ≤ θ * ρ6 := mul_le_mul_of_nonneg_left hρ9r hθ0.le
      rw [hρ9]; linarith
    have h3 : 2 * Q * (ρ9 + ρ10) ≤ ρ6 := by
      nlinarith only [h2, hQθ, hQ0, hρ60, hθ0]
    linarith
  · -- the error of the first half of the ninth step
    unfold err9
    rw [← hδdef, ← hQdef]
    try rw [← hdR]
    have hQe : Q = (32 / δ ^ 4) ^ (T.card ^ 2) := by rw [hQdef]; unfold qbar; rw [← hδdef]
    set K' : ℝ := dR ^ 2 * (400 * dR * Cb / δ ^ 4) ^ 2 * Q * (131072 / (δ ^ 4) ^ 4) with hK'
    have hK'0 : 0 ≤ K' := by rw [hK']; positivity
    have hKe : lqK T.card (δ ^ 4) ρ6 * ρ9 * ρ10 = θ ^ 5 * K' := by
      unfold lqK lqτ
      rw [← hCb, ← hdR, ← hQe, hK', hρ10, hρ9]
      field_simp
      ring
    have hK'H : K' ≤ H ^ 10452 := by
      have h1 : dR ^ 2 ≤ H ^ (1 * 2) := powH 2 (by positivity) hdH
      have h2 : 400 * dR * Cb / δ ^ 4 ≤ H ^ (1 + 1 + 2 + 1740) := by
        rw [div_eq_mul_one_div]
        exact mH (by positivity) (by positivity)
          (mH (by positivity) hCb0 (mH (by norm_num) (by positivity) (hcH 400 (by norm_num)) hdH)
            hCbH) hδ4inv
      have h3 : (400 * dR * Cb / δ ^ 4) ^ 2 ≤ H ^ ((1 + 1 + 2 + 1740) * 2) :=
        powH 2 (by positivity) h2
      have h4 : 131072 / (δ ^ 4) ^ 4 ≤ H ^ (1 + 1740 * 4) := by
        have : 1 / (δ ^ 4) ^ 4 ≤ H ^ (1740 * 4) := by
          rw [one_div, ← inv_pow]; rw [one_div] at hδ4inv; exact powH 4 (by positivity) hδ4inv
        rw [div_eq_mul_one_div]
        exact mH (by norm_num) (by positivity) (hcH 131072 (by norm_num)) this
      have := mH (by positivity) (by positivity)
        (mH (by positivity) hQ0 (mH (by positivity) (by positivity) h1 h3) hQH) h4
      rw [hK']
      calc _ ≤ _ := this
        _ = H ^ 10452 := by norm_num
    have t1 : 2 * (50 * dR * (2 * Q * ρ10) / ρ5) ≤ θ * (200 * dR * Q) := by
      have h1 : ρ10 ≤ θ * ρ5 := by
        calc ρ10 ≤ θ * ρ9 := hρ10r
          _ ≤ θ * ρ5 := mul_le_mul_of_nonneg_left (hρ9r.trans hρ6r) hθ0.le
      have h0 : 0 ≤ 200 * dR * Q := by positivity
      calc 2 * (50 * dR * (2 * Q * ρ10) / ρ5) = 200 * dR * Q * ρ10 / ρ5 := by ring
        _ ≤ 200 * dR * Q * (θ * ρ5) / ρ5 := by gcongr
        _ = θ * (200 * dR * Q) := by field_simp
    have t2 : 50 * dR * (2 * Q * ρ9) / ρ6 = θ * (100 * dR * Q) := by
      rw [hρ9]; field_simp; ring
    have t3 : 2 * (2 * Real.pi * (2 * Q * (lqK T.card (δ ^ 4) ρ6 * ρ9 * ρ10))) ≤
        θ * (32 * Q * K') := by
      rw [hKe]
      have h5 : θ ^ 5 ≤ θ := pow_le_of_le_one hθ0.le hθ1 (by norm_num)
      have hQK : 0 ≤ Q * K' := by positivity
      have : θ ^ 5 * (Q * K') ≤ θ * (Q * K') := mul_le_mul_of_nonneg_right h5 hQK
      calc 2 * (2 * Real.pi * (2 * Q * (θ ^ 5 * K'))) = 8 * Real.pi * (θ ^ 5 * (Q * K')) := by
            ring
        _ ≤ 8 * Real.pi * (θ * (Q * K')) := mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 8 * 4 * (θ * (Q * K')) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = θ * (32 * Q * K') := by ring
    have hM : 300 * dR * Q + 32 * Q * K' ≤ H ^ 10455 := by
      have h1 : 300 * dR * Q ≤ H ^ (1 + 1 + 1) :=
        mH (by positivity) hQ0 (mH (by norm_num) (by positivity) (hcH 300 (by norm_num)) hdH) hQH
      have h2 : 32 * Q * K' ≤ H ^ (1 + 1 + 10452) :=
        mH (by positivity) hK'0 (mH (by norm_num) hQ0 (hcH 32 (by norm_num)) hQH) hK'H
      have h3 : H ^ (1 + 1 + 1) ≤ H ^ (1 + 1 + 10452) := pow_le_pow_right₀ hH1 (by norm_num)
      have h2H : (2 : ℝ) ≤ H := by simpa using hcH 2 (by norm_num)
      have h4 : 2 * H ^ (1 + 1 + 10452) ≤ H ^ 10455 := by
        calc 2 * H ^ (1 + 1 + 10452) ≤ H * H ^ (1 + 1 + 10452) :=
              mul_le_mul_of_nonneg_right h2H (by positivity)
          _ = H ^ 10455 := by ring
      calc 300 * dR * Q + 32 * Q * K' ≤ H ^ (1 + 1 + 10452) + H ^ (1 + 1 + 10452) :=
            add_le_add (h1.trans h3) h2
        _ = 2 * H ^ (1 + 1 + 10452) := by ring
        _ ≤ _ := h4
    have S9 := key (M := 300 * dR * Q + 32 * Q * K') (a := 10455) (b := 217 * 1 + 1)
      (by positivity) hM (epsc 1 4 (by norm_num) (by norm_num)) (by norm_num)
    rw [pow_one] at S9
    have e : θ * (300 * dR * Q + 32 * Q * K') =
        θ * (200 * dR * Q) + θ * (100 * dR * Q) + θ * (32 * Q * K') := by ring
    linarith
  · -- `hsep`
    have S20 := key (M := 7200 * dR) (a := 2) (b := 217 * 4 + 1) (by positivity)
      (by simpa using mH (by norm_num) (by positivity) (hcH 7200 (by norm_num)) hdH)
      (epsc 4 1024 (by norm_num) (by norm_num)) (by norm_num)
    have e : ((c0 / 4) ^ 2 / 2) ^ 2 = c0 ^ 4 / 1024 := by ring
    rw [e]
    have h1 : ρ10 ≤ θ * ρ9 := hρ10r
    have h0 : 0 ≤ 7200 * dR := by positivity
    calc 7200 * dR * ρ10 ≤ 7200 * dR * (θ * ρ9) := mul_le_mul_of_nonneg_left h1 h0
      _ = θ * (7200 * dR) * ρ9 := by ring
      _ ≤ c0 ^ 4 / 1024 * ρ9 := mul_le_mul_of_nonneg_right S20 hρ90.le
  · have : ρ10 ≤ ρ9 / 16 := by nlinarith only [hρ10r, hθ16, hρ90]
    have : ρ9 ≤ ρA / 16 := by
      have : ρ9 ≤ ρ6 := hρ9r
      have : ρ6 ≤ ρ5 := hρ6r
      have : ρ5 ≤ ρA / 16 := hρ5A
      linarith
    linarith
  · have : ρ10 ≤ ρ9 / 16 := by nlinarith only [hρ10r, hθ16, hρ90]
    have : ρ9 ≤ ρA / 16 := by
      have : ρ9 ≤ ρ6 := hρ9r
      have : ρ6 ≤ ρ5 := hρ6r
      have : ρ5 ≤ ρA / 16 := hρ5A
      linarith
    linarith
  · -- `hsh`
    rw [hσ0]
    have h1 : r' ≤ θ * ρ0 := hr'le
    have h2 : ρ5 ≤ θ * ρ0 := by linarith
    have h3 : ρ6 ≤ θ * ρ0 := by linarith
    have h4 : ρ9 ≤ θ * ρ0 := by linarith
    have h5 : θ ^ 2 * ρ0 ≤ θ * ρ0 := mul_le_mul_of_nonneg_right hθ2 hρ0.le
    have h6 : 2 * Q * ρ9 ≤ 2 * Q * (θ * ρ0) := mul_le_mul_of_nonneg_left h4 (by positivity)
    have h7 : 2 * Q * (θ * ρ0) ≤ ρ0 / 32 := by nlinarith only [hQθ, hρ0]
    have h8 : θ * ρ0 ≤ ρ0 / 1000 := by
      have : θ ≤ 1 / 1000 := hθs.trans (by norm_num)
      nlinarith only [this, hρ0]
    linarith
  · -- `hfin`
    rw [hσ0]
    have hsum : 2 * (θ ^ 2 * ρ0) + r' + r' + ρ5 + ρ6 + 2 * Q * ρ9 ≤ θ * (6 + 2 * Q) * ρ0 := by
      have h1 : r' ≤ θ * ρ0 := hr'le
      have h2 : ρ5 ≤ θ * ρ0 := by linarith
      have h3 : ρ6 ≤ θ * ρ0 := by linarith
      have h4 : ρ9 ≤ θ * ρ0 := by linarith
      have h5 : θ ^ 2 * ρ0 ≤ θ * ρ0 := mul_le_mul_of_nonneg_right hθ2 hρ0.le
      have h6 : 2 * Q * ρ9 ≤ 2 * Q * (θ * ρ0) := mul_le_mul_of_nonneg_left h4 (by positivity)
      have e : θ * (6 + 2 * Q) * ρ0 = 6 * (θ * ρ0) + 2 * Q * (θ * ρ0) := by ring
      linarith
    have hM : 50 * sR * (6 + 2 * Q) ≤ H ^ 4 := by
      have h1 : 6 + 2 * Q ≤ 8 * Q := by linarith
      have h2 : 8 * Q ≤ H ^ 2 := by simpa using mH (by norm_num) hQ0 (hcH 8 (by norm_num)) hQH
      have h3 : 50 * sR ≤ H ^ 2 := by
        simpa using mH (by norm_num) (by positivity) (hcH 50 (by norm_num)) hscH
      have := mul_le_mul h3 (h1.trans h2) (by positivity) (by positivity)
      rw [← pow_add] at this
      exact this
    have S24 := key (M := 50 * sR * (6 + 2 * Q)) (a := 4) (b := 217 * 4 + 1)
      (by positivity) hM (epsc 4 4096 (by norm_num) (by norm_num)) (by norm_num)
    have e : ((c0 / 4) ^ 2) ^ 2 / 16 = c0 ^ 4 / 4096 := by ring
    rw [e, div_le_iff₀ hρ0]
    have h0 : 0 ≤ 50 * sR := by positivity
    calc 50 * sR * (2 * (θ ^ 2 * ρ0) + r' + r' + ρ5 + ρ6 + 2 * Q * ρ9) ≤
        50 * sR * (θ * (6 + 2 * Q) * ρ0) := mul_le_mul_of_nonneg_left hsum h0
      _ = θ * (50 * sR * (6 + 2 * Q)) * ρ0 := by ring
      _ ≤ c0 ^ 4 / 4096 * ρ0 := mul_le_mul_of_nonneg_right S24 hρ0.le
  · -- the dilation
    rw [hkH]; exact h2QH
  · -- the final correlation
    unfold u3κ
    have h1 := hc0pow 4
    have h2 : η ^ (2 ^ 20) ≤ η ^ (217 * 4) * η := by
      rw [← pow_succ]
      exact pow_le_pow_of_le_one hη0.le (hη.trans (by norm_num)) (by norm_num)
    have h3 : η ≤ 1 / 4096 := hη.trans (by norm_num)
    have h4 : η ^ (217 * 4) * η ≤ c0 ^ 4 * (1 / 4096) :=
      mul_le_mul h1 h3 hη0.le (by positivity)
    exact h2.trans (h4.trans (le_of_eq (by ring)))

end

end GT
end File_GT_InvU3NumC

section File_GT_InvU3Thm
/-!
# The local inverse `U³` theorem (Green–Tao, Theorem 8.1): the proof
-/

open Finset KM ComplexConjugate

namespace GT

noncomputable section

set_option maxHeartbeats 8000000 in
/-- **Theorem 8.1** (local inverse `U³` theorem). -/
theorem inv_u3 {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)}
    (hS : ∃ s ∈ S, s ≠ 0)
    {s : ℕ} (hs : S.card ≤ s) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 ^ 30)
    {ρ0 θ : ℝ} (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1) (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η)
    (hpl : u3P s η θ ρ0 ≤ p) (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hU : η ≤ ‖u3avg S ρ0 (θ * ρ0) (θ ^ 2 * ρ0) f‖) :
    ∃ (k : ℕ) (S' : Finset (ZMod p)) (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
      1 ≤ k ∧ (k : ℝ) ≤ u3k s η ∧ S ⊆ S' ∧ (S'.card : ℝ) ≤ S.card + u3J η ∧
      LocQuad (sBohr S' 0 (2 * (θ ^ u3T η * ρ0))) φ ∧
      u3κ η ≤ ∑ n, regP S ρ0 n * ‖∑ m, (regP S' (θ ^ u3T η * ρ0) m : ℂ) *
        (f (n + k * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ := by
  have hSne : S.Nonempty := by obtain ⟨x, hx, -⟩ := hS; exact ⟨x, hx⟩
  have hθs := theta_le_small hη0 hη1 hθ0.le hθ
  have hθ16 : θ ≤ 1 / 16 := hθs.trans (by norm_num)
  have hθ1 : θ ≤ 1 := by linarith
  have hη1' : η ≤ 1 := hη1.trans (by norm_num)
  -- steps one to three
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
    num_front (p := p) hs hη0 hη1 hθ0 hθ hρ0 hρ01 hpl
  obtain ⟨Ω, ξ, As, c, hΩb, hΩ, hAs, hW⟩ := u3_front hp hSne (ρ4 := θ ^ 4 * ρ0) (ρh := θ ^ 2 * ρ0)
    (ρv := θ ^ 3 * ρ0) (L := u3L) (m := u3m η) hη0 hη1' hρ0 (by positivity)
    (by positivity) (by positivity) (by positivity) f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
    (by positivity) (by positivity) f11 f12 f13 (by unfold u3L; norm_num) (u3m_ge hη0 hη1) f14 f15
    (u3m_mL hη0 hη1) f16 f hf hU
  -- steps four to six
  set NJ := ⌊u3J η⌋₊ with hNJ
  set R : ℕ → ℝ := fun t => θ ^ (t + 2) * ρ0 with hR
  have hR0 : ∀ t, 0 < R t := fun t => by simp only [hR]; positivity
  have hRk : ∀ t, R (t + 1) ≤ θ * R t := fun t => by simp only [hR]; rw [pow_succ]; nlinarith [hR0 t]
  have hR1 : R 0 ≤ 1 := by
    simp only [hR]
    have : θ ^ (0 + 2) ≤ 1 := pow_le_one₀ hθ0.le hθ1
    nlinarith
  have hQ0 : u3c3 η ≤ QW R (Wt S (θ ^ 3 * ρ0) u3L ξ As) S c 0 := by
    have e : QW R (Wt S (θ ^ 3 * ρ0) u3L ξ As) S c 0 =
        qavg S (θ ^ 4 * ρ0) (θ ^ 3 * ρ0) (θ ^ 2 * ρ0) c (Wt S (θ ^ 3 * ρ0) u3L ξ As) := by
      simp only [QW, hR]
    rw [e]; unfold u3c3; exact hW
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13⟩ :=
    num_mid hs hη0 hη1 hθ0 hθ hρ0 hρ01
  set r := θ ^ (20 * NJ + 90) * ρ0 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨T, k, ξ'', a0, ξ0, hST, hTc, hkK, hlin, hsa0, hQ⟩ := u3_mid hR0 hRk hθ0.le hθ16 hR1
    f hf hη0 (ρ0 := ρ0) (by positivity) (by positivity : (0 : ℝ) ≤ θ ^ 2 * ρ0) Ω ξ hΩb hΩ As hAs
    (by positivity) (by unfold u3L; norm_num) c (u3c3_pos hη0 hη1)
    (pow_pos (u3c3_pos hη0 hη1) 16) m0 hQ0 m1 m2 m3 m4 m5 m6 m7 m8 m9
    (r' := θ * r) (by positivity) (by nlinarith) m10 m11 (by positivity) f1 m12 m13
  -- steps seven to nine
  have hTs : T.card ≤ s + NJ := by omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
      b19, b20, b21, b22, b23, b24, b25, b26⟩ :=
    num_back (S := S) (T := T) hs hTs (Finset.card_pos.2 (hSne.mono hST)) hη0 hη1 hθ0 hθ hρ0 hρ01 (r := r) (r' := θ * r)
      (r3 := θ ^ 2 * r) (ρA := θ ^ 3 * r) (ρ4 := θ ^ 4 * r) (ρ5 := θ ^ 5 * r)
      (ρ6 := θ ^ 6 * r) (ρ9 := θ ^ 7 * r) (ρ10 := θ ^ u3T η * ρ0) rfl rfl (by ring) (by ring)
      (by ring) (by ring) (by ring) (by ring)
      (by rw [hr]; unfold u3T; ring) rfl rfl rfl
  obtain ⟨q, hq1, hqb, φ, β, hφ, hcorr⟩ := u3_back hp hS hST f hf ξ''
    (B := 24 * (1 / (θ ^ 3 * ρ0))) (by positivity) hlin a0 ξ0 hsa0 hρ0 (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) b0 hQ b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
    b16 b17 b18 b19 b20 b21 b22 b23 b24
  refine ⟨2 * q, T, φ, β, by omega, ?_, hST, ?_, hφ, b26.trans hcorr⟩
  · have : ((2 * q : ℕ) : ℝ) ≤ 2 * qbar T (u3c3 η * η / 288) (θ ^ 5 * r) (θ ^ 6 * r) := by
      push_cast; linarith
    linarith
  · have h1 : (T.card : ℝ) ≤ S.card + k := by exact_mod_cast hTc
    have h2 : (k : ℝ) ≤ NJ := by
      have : k ≤ NJ := by omega
      exact_mod_cast this
    have h3 : (NJ : ℝ) ≤ u3J η := Nat.floor_le (le_trans (by positivity) (u3J_ge hη0 hη1))
    linarith

end

end GT
end File_GT_InvU3Thm

open Finset KM ComplexConjugate
open GT in
theorem solution {p : ℕ} [NeZero p] (hp : p.Prime) {S : Finset (ZMod p)}
    (hS : ∃ s ∈ S, s ≠ 0)
    {s : ℕ} (hs : S.card ≤ s) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2 ^ 30)
    {ρ0 θ : ℝ} (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1) (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η)
    (hpl : u3P s η θ ρ0 ≤ p) (f : ZMod p → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hU : η ≤ ‖u3avg S ρ0 (θ * ρ0) (θ ^ 2 * ρ0) f‖) :
    ∃ (k : ℕ) (S' : Finset (ZMod p)) (φ : ZMod p → UnitAddCircle) (β : ZMod p → ZMod p),
      1 ≤ k ∧ (k : ℝ) ≤ u3k s η ∧ S ⊆ S' ∧ (S'.card : ℝ) ≤ S.card + u3J η ∧
      LocQuad (sBohr S' 0 (2 * (θ ^ u3T η * ρ0))) φ ∧
      u3κ η ≤ ∑ n, regP S ρ0 n * ‖∑ m, (regP S' (θ ^ u3T η * ρ0) m : ℂ) *
        (f (n + k * m) * ec (-(φ m) - ZMod.toAddCircle (β n * m)))‖ :=
  @GT.inv_u3 p _ hp S hS s hs η hη0 hη1 ρ0 θ hρ0 hρ01 hθ0 hθ hpl f hf hU

