-- Prove2me | solution 1 for FourExp.construction_count
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:34:16.075031+00:00
-- url     : https://prove2.me/submissions/94995e8d-cefd-4981-9be6-9aa613a51f60

import Mathlib

namespace FourExp

/-- The purely real core inequality. -/
theorem agentC_core (Nr s r K a b c S n P ℓ Y₁ Y₂ X : ℝ)
    (hX : 0 ≤ X) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) (hK : K = (Y₁ + Y₂) * X)
    (hNr : 784 + 2240 * K ≤ Nr)
    (hs1 : 1 ≤ s) (hsr : s ≤ r) (hrr : r * r = Nr) (hr22 : 22 ≤ r)
    (ha1 : a ≤ Nr / s) (ha2 : Nr / s < a + 1)
    (hb1 : b ≤ Nr * s) (hb2 : Nr * s < b + 1)
    (hS1 : S ≤ Nr ^ 2 * s) (hS2 : Nr ^ 2 * s < S + 1)
    (hc : S ≤ 2 * c + 1)
    (hn : n = S * (2 * Nr) * (2 * Nr))
    (hP0 : 0 ≤ P) (hP : P ≤ Nr) (hℓ : 1 ≤ ℓ) :
    n / (1 / 20 : ℝ) + 2 * (1 + P) / ((1 / 20 : ℝ) * ℓ) *
        (1 + (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X))
      ≤ 14 * a * (14 * b) * c := by
  have hr0 : 0 ≤ r := by linarith
  have h22r : 22 * r ≤ r * r := mul_le_mul_of_nonneg_right hr22 hr0
  have hNr0 : 0 < Nr := by linarith
  have hN1 : 1 ≤ Nr := by linarith
  have hs0 : 0 < s := by linarith
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have h22s : 22 * s ≤ Nr := by linarith
  set A := Nr / s with hA
  have hAs : A * s = Nr := div_mul_cancel₀ Nr hs0.ne'
  have hrs : r * s ≤ r * r := mul_le_mul_of_nonneg_left hsr hr0
  have hAr : r ≤ A := by
    rw [hA, le_div_iff₀ hs0]; linarith
  have hAN : A ≤ Nr := div_le_self hNr0.le hs1
  have hNs : Nr ≤ Nr * s := le_mul_of_one_le_right hNr0.le hs1
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab : (A - 1) * (Nr * s - 1) ≤ a * b :=
    mul_le_mul (by linarith) (by linarith) (by linarith) ha0
  have heq : (A - 1) * (Nr * s - 1) = Nr ^ 2 - A - Nr * s + 1 := by
    linear_combination Nr * hAs
  have hab2 : Nr ^ 2 - 2 * Nr * s ≤ a * b := by linarith
  have hcl : (Nr ^ 2 * s - 2) / 2 ≤ c := by linarith
  have hX1' : 0 ≤ Nr * (Nr - 2 * s) := mul_nonneg hNr0.le (by linarith)
  have hX1 : 0 ≤ Nr ^ 2 - 2 * Nr * s := by linarith
  have hNN : Nr * 1 ≤ Nr * Nr := mul_le_mul_of_nonneg_left hN1 hNr0.le
  have hN2s : Nr ^ 2 * 1 ≤ Nr ^ 2 * s := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have hX2 : 0 ≤ (Nr ^ 2 * s - 2) / 2 := by linarith
  have habc : (Nr ^ 2 - 2 * Nr * s) * ((Nr ^ 2 * s - 2) / 2) ≤ a * b * c :=
    mul_le_mul hab2 hcl hX2 (by linarith)
  have hS4 : S * (4 * Nr ^ 2) ≤ Nr ^ 2 * s * (4 * Nr ^ 2) :=
    mul_le_mul_of_nonneg_right hS1 (by positivity)
  have hn1 : n / (1 / 20 : ℝ) ≤ 80 * Nr ^ 4 * s := by
    have e : n / (1 / 20 : ℝ) = 20 * (S * (4 * Nr ^ 2)) := by rw [hn]; ring
    rw [e]; linarith
  have hQ : (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X) ≤ 28 * Nr ^ 2 * s * K := by
    have ha' : a ≤ Nr * s := by linarith
    have hy1 : a * Y₁ ≤ Nr * s * Y₁ := mul_le_mul_of_nonneg_right ha' hY₁
    have hy2 : b * Y₂ ≤ Nr * s * Y₂ := mul_le_mul_of_nonneg_right hb1 hY₂
    have h1 : 14 * a * Y₁ + 14 * b * Y₂ ≤ 14 * (Nr * s) * (Y₁ + Y₂) := by linarith
    have h2 : 0 ≤ 2 * Nr * X := by positivity
    calc (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X) ≤ 14 * (Nr * s) * (Y₁ + Y₂) * (2 * Nr * X) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = 28 * Nr ^ 2 * s * K := by rw [hK]; ring
  have hQ0 : 0 ≤ 1 + (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X) := by positivity
  have hE : 2 * (1 + P) / ((1 / 20 : ℝ) * ℓ) *
        (1 + (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X)) ≤ 40 * (1 + Nr) * (1 + 28 * Nr ^ 2 * s * K) := by
    have heq2 : 2 * (1 + P) / ((1 / 20 : ℝ) * ℓ) = 40 * (1 + P) / ℓ := by
      field_simp; ring
    rw [heq2]
    have hl : (1 + Nr) * 1 ≤ (1 + Nr) * ℓ := mul_le_mul_of_nonneg_left hℓ (by linarith)
    have h1 : 40 * (1 + P) / ℓ ≤ 40 * (1 + Nr) := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc 40 * (1 + P) / ℓ * (1 + (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X))
        ≤ 40 * (1 + Nr) * (1 + (14 * a * Y₁ + 14 * b * Y₂) * (2 * Nr * X)) :=
          mul_le_mul_of_nonneg_right h1 hQ0
      _ ≤ 40 * (1 + Nr) * (1 + 28 * Nr ^ 2 * s * K) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- final polynomial inequality
  have hss : s * s ≤ s * r := mul_le_mul_of_nonneg_left hsr hs0.le
  have h196 : 196 * r ≤ 9 * Nr := by linarith
  have hNs3 : 0 ≤ Nr ^ 3 * s := by positivity
  have hT1 : 196 * Nr ^ 3 * (s * s) ≤ 9 * Nr ^ 4 * s := by
    have h1 : 196 * Nr ^ 3 * (s * s) ≤ 196 * Nr ^ 3 * (s * r) :=
      mul_le_mul_of_nonneg_left hss (by positivity)
    have h3 : Nr ^ 3 * s * (196 * r) ≤ Nr ^ 3 * s * (9 * Nr) := mul_le_mul_of_nonneg_left h196 hNs3
    linarith
  have hT2 : 40 * (1 + Nr) * (1 + 28 * Nr ^ 2 * s * K) + 196 * Nr ^ 2
      ≤ Nr ^ 3 * s * (276 + 2240 * K) := by
    have hNs1 : 1 ≤ Nr * s := by linarith
    have e1 : Nr ^ 2 * 1 ≤ Nr ^ 2 * (Nr * s) := mul_le_mul_of_nonneg_left hNs1 (by positivity)
    have e2 : Nr ^ 2 * s * K * 1 ≤ Nr ^ 2 * s * K * Nr :=
      mul_le_mul_of_nonneg_left hN1 (by positivity)
    have e3 : (1:ℝ) ≤ Nr ^ 2 := by linarith
    linarith
  have hT3 : Nr ^ 3 * s * (276 + 2240 * K) ≤ Nr ^ 3 * s * Nr :=
    mul_le_mul_of_nonneg_left (by linarith) hNs3
  have hexp : (Nr ^ 2 - 2 * Nr * s) * ((Nr ^ 2 * s - 2) / 2) * 196
      = 98 * Nr ^ 4 * s - 196 * Nr ^ 2 - 196 * Nr ^ 3 * (s * s) + 392 * Nr * s := by ring
  have hNs4 : 0 ≤ Nr ^ 4 * s := by positivity
  have hNs5 : 0 ≤ Nr * s := by positivity
  have hfin : 14 * a * (14 * b) * c = 196 * (a * b * c) := by ring
  rw [hfin]
  linarith

end FourExp

theorem solution (X Y₁ Y₂ : ℝ) (hX : 0 ≤ X) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ((((⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ) / (1 / 20 : ℝ)
              + 2 * (1 + (((⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ) ^ (1 / 20 : ℝ)) / ((1 / 20 : ℝ) * Real.log ((((⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ)))
                * (1 + (((14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) : ℕ) * Y₁ + ((14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊) : ℕ) * Y₂) * (((2 * N) : ℕ) * X))
            ≤ ((((14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊)) * ((14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊)) * (⌊(N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))⌋₊ / 2) : ℕ) : ℝ)) := by
  refine ⟨784 + ⌈2240 * ((Y₁ + Y₂) * X)⌉₊, fun N hN => ?_⟩
  have hNr : (784:ℝ) + 2240 * ((Y₁ + Y₂) * X) ≤ (N:ℝ) := by
    have h1 := Nat.le_ceil (2240 * ((Y₁ + Y₂) * X))
    have h2 : ((784 + ⌈2240 * ((Y₁ + Y₂) * X)⌉₊ : ℕ) : ℝ) < (N:ℝ) := by exact_mod_cast hN
    push_cast at h2; linarith
  have hK0 : 0 ≤ (Y₁ + Y₂) * X := by positivity
  have hN0 : (0:ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log (N:ℝ) := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9; linarith
  have hLN : Real.log (N:ℝ) ≤ N := by
    have := Real.log_le_sub_one_of_pos hN0; linarith
  have hs1 : 1 ≤ Real.sqrt (Real.log (N:ℝ)) := by
    rw [Real.one_le_sqrt]; exact hL1
  have hrr : Real.sqrt (N:ℝ) * Real.sqrt (N:ℝ) = N := Real.mul_self_sqrt hN0.le
  have hsr : Real.sqrt (Real.log (N:ℝ)) ≤ Real.sqrt (N:ℝ) := Real.sqrt_le_sqrt hLN
  have hr0 : 0 ≤ Real.sqrt (N:ℝ) := Real.sqrt_nonneg _
  have hr22 : 22 ≤ Real.sqrt (N:ℝ) := by nlinarith
  set s := Real.sqrt (Real.log (N:ℝ)) with hsdef
  set r := Real.sqrt (N:ℝ) with hrdef
  have hs0 : 0 < s := by linarith
  obtain ⟨a, ha1, ha2, hadef⟩ : ∃ a : ℕ, (a:ℝ) ≤ (N:ℝ) / s ∧ (N:ℝ) / s < a + 1 ∧
      ⌊(N:ℝ) / s⌋₊ = a := ⟨_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _, rfl⟩
  obtain ⟨b, hb1, hb2, hbdef⟩ : ∃ b : ℕ, (b:ℝ) ≤ (N:ℝ) * s ∧ (N:ℝ) * s < b + 1 ∧
      ⌊(N:ℝ) * s⌋₊ = b := ⟨_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _, rfl⟩
  obtain ⟨S, hS1, hS2, hSdef⟩ : ∃ S : ℕ, (S:ℝ) ≤ (N:ℝ) ^ 2 * s ∧ (N:ℝ) ^ 2 * s < S + 1 ∧
      ⌊(N:ℝ) ^ 2 * s⌋₊ = S := ⟨_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _, rfl⟩
  rw [hadef, hbdef, hSdef]
  have hc : (S:ℝ) ≤ 2 * ((S / 2 : ℕ) : ℝ) + 1 := by
    have : S ≤ 2 * (S / 2) + 1 := by omega
    exact_mod_cast this
  generalize S / 2 = c at hc ⊢
  push_cast
  have hSpos : (1:ℝ) ≤ S := by
    have : (1:ℝ) ≤ (N:ℝ) ^ 2 * s - 1 := by nlinarith
    have hS' : (1:ℝ) < S + 1 := by linarith
    have : (0:ℕ) < S := by exact_mod_cast (by linarith : (0:ℝ) < S)
    exact_mod_cast this
  set n : ℝ := (S:ℝ) * (2 * (N:ℝ)) * (2 * (N:ℝ)) with hn
  have hn3 : Real.exp 1 ≤ n := by
    have := Real.exp_one_lt_d9
    have : (4:ℝ) ≤ n := by rw [hn]; nlinarith
    linarith
  have hℓ : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hn3)]; exact hn3
  have hnN : n ≤ (N:ℝ) ^ 20 := by
    have h1 : n ≤ 4 * (N:ℝ) ^ 4 * s := by rw [hn]; nlinarith
    have hsN : s ≤ (N:ℝ) := by nlinarith
    have hN1 : (1:ℝ) ≤ N := by linarith
    have h2 : 4 * (N:ℝ) ^ 4 * s ≤ 4 * (N:ℝ) ^ 5 := by
      have : 4 * (N:ℝ) ^ 4 * s ≤ 4 * (N:ℝ) ^ 4 * N :=
        mul_le_mul_of_nonneg_left hsN (by positivity)
      nlinarith
    have h3 : 4 * (N:ℝ) ^ 5 ≤ (N:ℝ) ^ 20 := by
      have h4 : (4:ℝ) ≤ (N:ℝ) ^ 15 := by
        have : (N:ℝ) ≤ (N:ℝ) ^ 15 := by
          calc (N:ℝ) = (N:ℝ) ^ 1 := by ring
            _ ≤ (N:ℝ) ^ 15 := pow_le_pow_right₀ hN1 (by norm_num)
        linarith
      have : 4 * (N:ℝ) ^ 5 ≤ (N:ℝ) ^ 15 * (N:ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      calc 4 * (N:ℝ) ^ 5 ≤ (N:ℝ) ^ 15 * (N:ℝ) ^ 5 := this
        _ = (N:ℝ) ^ 20 := by ring
    linarith
  have hP : n ^ (1 / 20 : ℝ) ≤ (N:ℝ) := by
    have h1 : n ^ (1 / 20 : ℝ) ≤ ((N:ℝ) ^ 20) ^ (1 / 20 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hnN (by norm_num)
    have h2 : ((N:ℝ) ^ 20) ^ (1 / 20 : ℝ) = N := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    linarith
  have hP0 : 0 ≤ n ^ (1 / 20 : ℝ) := by positivity
  exact FourExp.agentC_core (N:ℝ) s r ((Y₁ + Y₂) * X) a b c S n _ _ Y₁ Y₂ X hX hY₁ hY₂ rfl
    hNr hs1 hsr hrr hr22 ha1 ha2 hb1 hb2 hS1 hS2 hc hn hP0 hP hℓ

#print axioms solution
