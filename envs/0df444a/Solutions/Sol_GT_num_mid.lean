-- Prove2me | solution 1 for GT.num_mid
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:41:12.826733+00:00
-- url     : https://prove2.me/submissions/7c1631e5-4ce4-4759-ab70-094deaa8c4f8

import Mathlib
import Definitions.Def_GreenTaoFourCore

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

end

end GT
end File_GT_InvU3NumA

section File_GT_InvU3NumB
/-!
# Numerical bookkeeping for the local inverse `U³` theorem: steps four to six
-/

open Finset KM

namespace GT

noncomputable section

lemma u3NJ_ge {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30) : u3J η / 2 ≤ (⌊u3J η⌋₊ : ℝ) := by
  have hJ := u3J_ge hη0 hη
  have hX := u3X_ge hη0 hη
  have h1 : (1 : ℝ) ≤ u3J η := by linarith [show (1 : ℝ) ≤ 2 ^ 30 by norm_num]
  have := Nat.lt_floor_add_one (u3J η)
  linarith

lemma u3NJ_le {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30) : (⌊u3J η⌋₊ : ℝ) ≤ u3J η :=
  Nat.floor_le (le_trans (by positivity) (u3J_ge hη0 hη))

set_option maxHeartbeats 4000000 in
/-- The numerical hypotheses of steps four to six. -/
theorem num_mid {s sc : ℕ} (hsc : sc ≤ s) {η θ ρ0 : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
    (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η) (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1) :
    0 < 1 / (20 * (⌊u3J η⌋₊ : ℝ)) ∧
    20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) ≤ u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 ∧
    1 + 20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) ≤
      20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) * ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ) ∧
    (u3L * 300 + u3c3 η / 8 * 1600) * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ ≤
      u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 ∧
    7200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ ≤ (u3c3 η ^ 16 / 2) ^ 2 ∧
    (350 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) + 13) * θ ≤ u3c3 η ^ 16 / 8 ∧
    u3L * (50 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) ≤ u3c3 η / 4 ∧
    2 * √(√(u3c3 η ^ 16) + 200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) ≤ u3c3 η / 8 ∧
    2 / (u3L * (1 / 200)) + 1700 * (√(u3c3 η ^ 16) +
      200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) / (u3c3 η / 2) ^ 2 ≤ 1 / 1000 ∧
    30 * (√(√(u3c3 η ^ 16) + 200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) +
      150 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) / (u3c3 η / 8) ^ 2 ≤ 1 / 1000 ∧
    4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) ≤ θ ^ (20 * (⌊u3J η⌋₊ + 1) + 2) * ρ0 ∧
    50 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) /
      (θ ^ (20 * (⌊u3J η⌋₊ + 1) + 2) * ρ0) ≤ 1 / 1000 ∧
    4 * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0)) ≤ θ * ρ0 ∧
    2 * (50 * (sc : ℝ) * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0)) / (θ * ρ0)) +
      50 * (sc : ℝ) * (θ * ρ0) / ρ0 +
      2 * (2 * Real.pi * (9 * (1 / (θ ^ 3 * ρ0)) * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0))))
      ≤ η / 16 := by
  have hθs := theta_le_small hη0 hη hθ0.le hθ
  have hθ1 : θ ≤ 1 / 16 := hθs.trans (by norm_num)
  have hθ1' : θ ≤ 1 := by linarith
  set NJ := ⌊u3J η⌋₊ with hNJ
  set c3 := u3c3 η with hc3def
  have hc3 : η ^ 215 ≤ c3 := u3c3_ge hη0 hη
  have hc3p : 0 < c3 := u3c3_pos hη0 hη
  have hc3le : c3 ≤ 1 / 2 ^ 30 := u3c3_le' hη0 hη
  have hc31 : c3 ≤ 1 := hc3le.trans (by norm_num)
  have hX := u3X_ge hη0 hη
  have hNJ2 := u3NJ_ge hη0 hη
  have hNJJ := u3NJ_le hη0 hη
  have hJ := u3J_ge hη0 hη
  have hNJ1 : (1 : ℝ) ≤ NJ := by linarith [show (1 : ℝ) ≤ 2 ^ 30 by norm_num]
  set d := ((sc : ℝ) + ((NJ + 1 : ℕ) : ℝ)) with hd
  have hd0 : 0 ≤ d := by positivity
  have hdD : d ≤ u3D s η := by
    have : (sc : ℝ) ≤ s := by exact_mod_cast hsc
    rw [hd]; unfold u3D; push_cast; linarith
  have hdH : d ≤ u3H s η ^ 1 := by rw [pow_one]; exact le_H_of_le_D hη0 hη hdD
  -- `θ * (c * d) ≤ η ^ k / c'`
  have key : ∀ (c c' : ℝ) (k : ℕ), k ≤ 100000 → 0 ≤ c → c ≤ 2 ^ 30 → 0 < c' → c' ≤ 2 ^ 30 →
      θ * (c * d) ≤ η ^ k / c' := fun c c' k hk hc0 hc hc'0 hc' =>
    thetaM hη0 hη hθ0.le hθ (by positivity) (mulH hη0 hη hc0 hd0 (constH hη0 hη hc) hdH)
      (epsH hη0 hη k hc'0 hc') (by omega)
  have hc3pow : ∀ k : ℕ, η ^ (215 * k) ≤ c3 ^ k := fun k => by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hc3 k
  have hsq16 : √(c3 ^ 16) = c3 ^ 8 := by
    rw [show c3 ^ 16 = (c3 ^ 8) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  -- the basic smallness `200 d θ ≤ c3^8`
  have hT1 : 200 * d * θ ≤ c3 ^ 8 := by
    have h := key 200 1 (215 * 8) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    rw [div_one] at h
    have := hc3pow 8
    nlinarith
  have hc38 : c3 ^ 8 ≤ c3 ^ 2 / 512 := by
    have h6 : c3 ^ 6 ≤ 1 / 512 := by
      calc c3 ^ 6 ≤ c3 := pow_le_of_le_one hc3p.le hc31 (by norm_num)
        _ ≤ 1 / 512 := hc3le.trans (by norm_num)
    have : c3 ^ 8 = c3 ^ 6 * c3 ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg c3]
  have hθd : 0 ≤ d * θ := by positivity
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `1 / NJ ≤ c3^33 / 2048`
    have e : 20 * (1 / (20 * (NJ : ℝ))) = 1 / NJ := by field_simp
    rw [e, show c3 / 8 * (c3 ^ 16 / 8) ^ 2 / 4 = c3 ^ 33 / 2048 by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 := hc3pow 33
    -- `NJ * η^7095 ≥ 2048`
    have hJX : u3J η = (1 / η) ^ (2 ^ 24) := rfl
    have h2 : (2048 : ℝ) * 2 ≤ u3J η * η ^ (215 * 33) := by
      rw [hJX]
      have e2 : (1 / η) ^ (2 ^ 24) * η ^ (215 * 33) = (1 / η) ^ (2 ^ 24 - 215 * 33) *
          ((1 / η) * η) ^ (215 * 33) := by
        rw [mul_pow, ← mul_assoc, ← pow_add]; norm_num
      rw [e2, show (1 / η) * η = 1 by field_simp, one_pow, mul_one]
      calc (2048 : ℝ) * 2 ≤ (1 / η) ^ 1 := by rw [pow_one]; linarith [show (4096 : ℝ) ≤ 2 ^ 30 by norm_num]
        _ ≤ _ := pow_le_pow_right₀ (le_trans (by norm_num) hX) (by norm_num)
    have : 2048 * 2 ≤ 2 * NJ * c3 ^ 33 := by
      calc (2048 : ℝ) * 2 ≤ u3J η * η ^ (215 * 33) := h2
        _ ≤ (2 * NJ) * c3 ^ 33 := by gcongr; linarith
    linarith
  · have e : 20 * (1 / (20 * (NJ : ℝ))) = 1 / NJ := by field_simp
    rw [e]; push_cast
    field_simp
    linarith
  · have h := key (10 ^ 6 * 300 + 200) 2048 (215 * 33) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have h1 := hc3pow 33
    have e : u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 = c3 ^ 33 / 2048 := by ring
    rw [e]
    have : (u3L * 300 + c3 / 8 * 1600) ≤ 10 ^ 6 * 300 + 200 := by unfold u3L; nlinarith
    calc (u3L * 300 + u3c3 η / 8 * 1600) * d * θ ≤ θ * ((10 ^ 6 * 300 + 200) * d) := by
          rw [← hc3def]; nlinarith
      _ ≤ η ^ (215 * 33) / 2048 := h
      _ ≤ _ := by gcongr
  · have h := key 7200 4 (215 * 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have h1 := hc3pow 32
    have e : (u3c3 η ^ 16 / 2) ^ 2 = c3 ^ 32 / 4 := by ring
    rw [e]
    calc 7200 * d * θ = θ * (7200 * d) := by ring
      _ ≤ _ := h
      _ ≤ _ := by gcongr
  · have h := key 363 8 (215 * 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    have h1 := hc3pow 16
    have hd1 : 1 ≤ d := by rw [hd]; push_cast; linarith [show (0 : ℝ) ≤ sc by positivity]
    calc (350 * d + 13) * θ ≤ θ * (363 * d) := by nlinarith
      _ ≤ _ := h
      _ ≤ _ := by gcongr
  · have h := key (10 ^ 6 * 50) 4 215 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    unfold u3L
    calc (10 : ℝ) ^ 6 * (50 * d * θ) = θ * (10 ^ 6 * 50 * d) := by ring
      _ ≤ _ := h
      _ ≤ _ := by gcongr
  · rw [hsq16]
    have : c3 ^ 8 + 200 * d * θ ≤ (c3 / 16) ^ 2 := by nlinarith
    have h2 : √(c3 ^ 8 + 200 * d * θ) ≤ c3 / 16 :=
      Real.sqrt_le_iff.2 ⟨by positivity, this⟩
    linarith
  · rw [hsq16]
    unfold u3L
    have h1 : 1700 * (c3 ^ 8 + 200 * d * θ) / (c3 / 2) ^ 2 ≤ 1 / 2000 := by
      rw [div_le_iff₀ (by positivity)]
      have h6 : c3 ^ 6 ≤ 1 / 2 ^ 30 := by
        calc c3 ^ 6 ≤ c3 := pow_le_of_le_one hc3p.le hc31 (by norm_num)
          _ ≤ 1 / 2 ^ 30 := hc3le
      have : c3 ^ 8 = c3 ^ 6 * c3 ^ 2 := by ring
      nlinarith [sq_nonneg c3]
    have h2 : (2 : ℝ) / (10 ^ 6 * (1 / 200)) = 1 / 2500 := by norm_num
    linarith
  · rw [hsq16]
    have h150 : 150 * d * θ ≤ c3 ^ 8 := by nlinarith
    have hs : √(c3 ^ 8 + 200 * d * θ) ≤ 2 * c3 ^ 4 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg (c3 ^ 4)]
    rw [div_le_iff₀ (by positivity)]
    have h6 : c3 ^ 2 ≤ 1 / 2 ^ 30 := by
      calc c3 ^ 2 ≤ c3 := pow_le_of_le_one hc3p.le hc31 (by norm_num)
        _ ≤ 1 / 2 ^ 30 := hc3le
    have h4 : c3 ^ 4 ≤ c3 ^ 2 * (1 / 2 ^ 30) := by
      have : c3 ^ 4 = c3 ^ 2 * c3 ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_left h6 (by positivity)
    have h8 : c3 ^ 8 ≤ c3 ^ 4 := pow_le_pow_of_le_one hc3p.le hc31 (by norm_num)
    nlinarith
  · -- `4 r ≤ R(20K)`
    have e : θ ^ (20 * NJ + 90) = θ ^ 68 * θ ^ (20 * (NJ + 1) + 2) := by
      rw [← pow_add]; congr 1; ring
    rw [e]
    have h68 : θ ^ 68 ≤ 1 / 16 := (pow_le_of_le_one hθ0.le hθ1' (by norm_num)).trans hθ1
    have : 0 < θ ^ (20 * (NJ + 1) + 2) * ρ0 := by positivity
    nlinarith
  · have e : 50 * d * (θ ^ (20 * NJ + 90) * ρ0) / (θ ^ (20 * (NJ + 1) + 2) * ρ0) =
        θ ^ 68 * (50 * d) := by
      rw [show θ ^ (20 * NJ + 90) = θ ^ 68 * θ ^ (20 * (NJ + 1) + 2) by rw [← pow_add]; congr 1; ring]
      field_simp
    rw [e]
    have h68 : θ ^ 68 ≤ θ := pow_le_of_le_one hθ0.le hθ1' (by norm_num)
    have h := key 50 1000 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rw [pow_zero] at h
    calc θ ^ 68 * (50 * d) ≤ θ * (50 * d) := by gcongr
      _ ≤ _ := h
  · have hr : θ ^ (20 * NJ + 90) * ρ0 ≤ ρ0 := by
      have : θ ^ (20 * NJ + 90) ≤ 1 := pow_le_one₀ hθ0.le hθ1'
      nlinarith
    have h3 : θ ^ 4 ≤ θ / 16 := by
      have : θ ^ 4 = θ * θ ^ 3 := by ring
      have h3' : θ ^ 3 ≤ 1 / 16 := (pow_le_of_le_one hθ0.le hθ1' (by norm_num)).trans hθ1
      rw [this]; nlinarith
    have : 0 ≤ θ ^ (20 * NJ + 90) * ρ0 := by positivity
    nlinarith
  · -- the error of Proposition 9.10
    set r := θ ^ (20 * NJ + 90) * ρ0 with hr
    have hr0 : 0 < r := by positivity
    have hrρ : r ≤ ρ0 := by
      have : θ ^ (20 * NJ + 90) ≤ 1 := pow_le_one₀ hθ0.le hθ1'
      rw [hr]; nlinarith
    have e1 : 50 * (sc : ℝ) * (θ ^ 4 * r) / (θ * ρ0) = θ * (50 * sc) * (θ ^ 2 * (r / ρ0)) := by
      field_simp
    have e2 : 50 * (sc : ℝ) * (θ * ρ0) / ρ0 = θ * (50 * sc) := by field_simp
    have e3 : 2 * (2 * Real.pi * (9 * (1 / (θ ^ 3 * ρ0)) * (θ ^ 4 * r))) =
        θ * (36 * Real.pi) * (r / ρ0) := by
      field_simp; norm_num
    rw [e1, e2, e3]
    have hrr : r / ρ0 ≤ 1 := by rw [div_le_one hρ0]; exact hrρ
    have hrr0 : 0 ≤ r / ρ0 := by positivity
    have hθ2 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0.le hθ1'
    have hsc0 : (0 : ℝ) ≤ sc := by positivity
    have hscH : (sc : ℝ) ≤ u3H s η ^ 1 := natH hη0 hη (card_le_D hη0 hη hsc)
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have h := thetaM hη0 hη (M := 150 * sc + 150) (ε := η / 16) (a := 2) (b := 2) hθ0.le hθ
      (by positivity) (by
        have h1 : (150 : ℝ) * sc + 150 ≤ 300 * sc + 150 := by linarith
        have h2 : (300 : ℝ) * sc + 150 ≤ u3H s η ^ 1 * u3H s η ^ 1 := by
          have hH := u3H_ge_one (s := s) hη0 hη
          have : (450 : ℝ) ≤ u3H s η := const_le_H hη0 hη (by norm_num)
          rw [pow_one] at hscH ⊢
          nlinarith
        have h3 : u3H s η ^ 1 * u3H s η ^ 1 = u3H s η ^ 2 := by ring
        linarith)
      (by simpa using epsH hη0 hη 1 (c := 16) (by norm_num) (by norm_num)) (by norm_num)
    have h1 : θ * (50 * sc) * (θ ^ 2 * (r / ρ0)) ≤ θ * (50 * sc) := by
      have : θ ^ 2 * (r / ρ0) ≤ 1 := by nlinarith
      have : 0 ≤ θ * (50 * sc) := by positivity
      nlinarith
    have h2 : θ * (36 * Real.pi) * (r / ρ0) ≤ θ * 150 := by
      have : θ * (36 * Real.pi) ≤ θ * 150 := by nlinarith
      nlinarith [mul_nonneg hθ0.le hrr0]
    nlinarith

end

end GT
end File_GT_InvU3NumB

open Finset KM
open GT in
theorem solution {s sc : ℕ} (hsc : sc ≤ s) {η θ ρ0 : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
    (hθ0 : 0 < θ) (hθ : θ ≤ u3θ s η) (hρ0 : 0 < ρ0) (hρ01 : ρ0 ≤ 1) :
    0 < 1 / (20 * (⌊u3J η⌋₊ : ℝ)) ∧
    20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) ≤ u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 ∧
    1 + 20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) ≤
      20 * (1 / (20 * (⌊u3J η⌋₊ : ℝ))) * ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ) ∧
    (u3L * 300 + u3c3 η / 8 * 1600) * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ ≤
      u3c3 η / 8 * (u3c3 η ^ 16 / 8) ^ 2 / 4 ∧
    7200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ ≤ (u3c3 η ^ 16 / 2) ^ 2 ∧
    (350 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) + 13) * θ ≤ u3c3 η ^ 16 / 8 ∧
    u3L * (50 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) ≤ u3c3 η / 4 ∧
    2 * √(√(u3c3 η ^ 16) + 200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) ≤ u3c3 η / 8 ∧
    2 / (u3L * (1 / 200)) + 1700 * (√(u3c3 η ^ 16) +
      200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) / (u3c3 η / 2) ^ 2 ≤ 1 / 1000 ∧
    30 * (√(√(u3c3 η ^ 16) + 200 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) +
      150 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * θ) / (u3c3 η / 8) ^ 2 ≤ 1 / 1000 ∧
    4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) ≤ θ ^ (20 * (⌊u3J η⌋₊ + 1) + 2) * ρ0 ∧
    50 * ((sc : ℝ) + ((⌊u3J η⌋₊ + 1 : ℕ) : ℝ)) * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0) /
      (θ ^ (20 * (⌊u3J η⌋₊ + 1) + 2) * ρ0) ≤ 1 / 1000 ∧
    4 * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0)) ≤ θ * ρ0 ∧
    2 * (50 * (sc : ℝ) * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0)) / (θ * ρ0)) +
      50 * (sc : ℝ) * (θ * ρ0) / ρ0 +
      2 * (2 * Real.pi * (9 * (1 / (θ ^ 3 * ρ0)) * (θ ^ 4 * (θ ^ (20 * ⌊u3J η⌋₊ + 90) * ρ0))))
      ≤ η / 16 :=
  @GT.num_mid s sc hsc η θ ρ0 hη0 hη hθ0 hθ hρ0 hρ01

