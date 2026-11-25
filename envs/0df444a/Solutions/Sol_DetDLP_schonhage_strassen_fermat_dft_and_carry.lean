-- Prove2me | solution 1 for DetDLP.schonhage_strassen_fermat_dft_and_carry
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:38.797803+00:00
-- url     : https://prove2.me/submissions/36c80d8a-0719-4cea-ae02-ad5bf461f911

import Mathlib

set_option autoImplicit false

private lemma carry_chain_props (B m : ℕ) (c z κ : ℕ → ℕ)
    (hB : 0 < B) (hκ0 : κ 0 = 0)
    (hstep : ∀ ℓ < m, c ℓ + κ ℓ = z ℓ + B * κ (ℓ + 1) ∧ z ℓ < B) :
    (∀ ℓ < m, z ℓ = (c ℓ + κ ℓ) % B ∧ κ (ℓ + 1) = (c ℓ + κ ℓ) / B) ∧
    (∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) =
      (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) + κ m * B ^ m ∧
    ((∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) < B ^ m →
      κ m = 0 ∧ (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) = ∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) := by
  have huniq : ∀ ℓ < m, z ℓ = (c ℓ + κ ℓ) % B ∧ κ (ℓ + 1) = (c ℓ + κ ℓ) / B := by
    intro ℓ hℓ
    obtain ⟨heq, hz_lt⟩ := hstep ℓ hℓ
    rw [heq]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hz_lt]
    · rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_zero_iff.mpr (Or.inr hz_lt), zero_add]
  have htele : ∀ k ≤ m,
      (∑ ℓ ∈ Finset.range k, c ℓ * B ^ ℓ) =
        (∑ ℓ ∈ Finset.range k, z ℓ * B ^ ℓ) + κ k * B ^ k := by
    intro k hk
    induction k with
    | zero => simp [hκ0]
    | succ k ih =>
      have hk_lt : k < m := Nat.lt_of_succ_le hk
      have ihk := ih (le_of_lt hk_lt)
      have hck := (hstep k hk_lt).1
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ihk]
      calc (∑ x ∈ Finset.range k, z x * B ^ x) + κ k * B ^ k + c k * B ^ k
          = (∑ x ∈ Finset.range k, z x * B ^ x) + (c k + κ k) * B ^ k := by ring
        _ = (∑ x ∈ Finset.range k, z x * B ^ x) + (z k + B * κ (k + 1)) * B ^ k := by rw [hck]
        _ = (∑ x ∈ Finset.range k, z x * B ^ x) + z k * B ^ k + κ (k + 1) * B ^ (k + 1) := by
            rw [pow_succ']; ring
  have htele_m := htele m (le_refl m)
  refine ⟨huniq, htele_m, fun hlt => ?_⟩
  have hκm : κ m = 0 := by
    by_contra hne
    have hge1 : 1 ≤ κ m := Nat.one_le_iff_ne_zero.mpr hne
    have hge_pow : B ^ m ≤ κ m * B ^ m := by
      simpa using Nat.mul_le_mul_right (B ^ m) hge1
    omega
  refine ⟨hκm, ?_⟩
  rw [htele_m, hκm, zero_mul, add_zero]

theorem solution :
    (∀ (d J n0 L L1 L2 : ℕ),
       1 ≤ d → 16 ≤ J → 64 * (d + 1) ≤ J ^ 2 → J ^ 2 < 256 * (d + 1) →
       1 ≤ n0 → n0 < J / 16 + 1 → 2 * n0 ≤ L → L < 4 * n0 →
       L1 ≤ L2 → L2 ^ 2 ≤ 2 * L →
       L ≤ J / 2 ∧
       L2 ^ 2 ≤ J ∧
       4 * d + 4 * J * (J + 1) < 1100 * (d + 1) ∧
       (2 * max L1 L2 * (J + 1) : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) ∧
    ((∀ (J μ step : ℕ),
        μ ≤ J → J = 2 ^ μ * step →
        let M := 2 ^ J + 1
        let ω : ZMod M := (2 : ZMod M) ^ step
        (2 : ZMod M) ^ J = -1 ∧
        ω ^ (2 ^ μ) = -1 ∧
        ω ^ (2 ^ (μ + 1)) = 1 ∧
        (-(2 : ZMod M) ^ (J - μ)) * ((2 : ZMod M) ^ μ) = 1) ∧
     (∀ (L1 L2 : ℕ) (ω : ℤ) (x : ℕ → ℤ) (t1 t2 : ℕ),
        ω ^ (L1 * L2) = 1 →
        ∑ j1 ∈ Finset.range L1, ∑ j2 ∈ Finset.range L2,
          x (L2 * j1 + j2) * ω ^ ((L2 * j1 + j2) * (t1 + L1 * t2)) =
        ∑ j2 ∈ Finset.range L2,
          ω ^ (L1 * j2 * t2) *
            (ω ^ (j2 * t1) * ∑ j1 ∈ Finset.range L1, ω ^ (L2 * j1 * t1) * x (L2 * j1 + j2)))) ∧
    (∀ (B m : ℕ) (c z κ : ℕ → ℕ),
       0 < B →
       κ 0 = 0 →
       (∀ ℓ < m, c ℓ + κ ℓ = z ℓ + B * κ (ℓ + 1) ∧ z ℓ < B) →
       (∀ ℓ < m, z ℓ = (c ℓ + κ ℓ) % B ∧ κ (ℓ + 1) = (c ℓ + κ ℓ) / B) ∧
       (∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) =
         (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) + κ m * B ^ m ∧
       ((∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) < B ^ m →
         κ m = 0 ∧ (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) = ∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ)) := by
  refine ⟨?_, ⟨?_, ?_⟩, carry_chain_props⟩
  · intro d J n0 L L1 L2 hd hJ16 hJ_lo hJ_hi hn0_pos hn0_hi hL_lo hL_hi hL12 hL2_sq
    have hL_le : L ≤ J / 2 := by omega
    have hL2_le_J : L2 ^ 2 ≤ J := by omega
    have h16J : 16 * J ≤ J ^ 2 := by nlinarith
    have hedge : 4 * d + 4 * J * (J + 1) < 1100 * (d + 1) := by nlinarith
    refine ⟨hL_le, hL2_le_J, hedge, ?_⟩
    rw [max_eq_right hL12]
    -- Compare 4th powers in ℝ
    have hLHS_nn : (0 : ℝ) ≤ (2 * L2 * (J + 1) : ℝ) := by positivity
    have hRHS_pos : (0 : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) := by positivity
    rw [← Real.rpow_lt_rpow_iff hLHS_nn (le_of_lt hRHS_pos) (by norm_num : (0 : ℝ) < 4)]
    have hRHS_pow : (136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) ^ (4 : ℝ) =
        (136 : ℝ) ^ 4 * ((d : ℝ) + 1) ^ 3 := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num
    have hLHS_pow : ((2 * L2 * (J + 1) : ℝ)) ^ (4 : ℝ) = ((2 * L2 * (J + 1) : ℝ)) ^ 4 :=
      Real.rpow_natCast _ 4
    rw [hLHS_pow, hRHS_pow]
    have hL2R : (L2 : ℝ) ^ 2 ≤ (J : ℝ) := by exact_mod_cast hL2_le_J
    have hJR_ge16 : (16 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ16
    have hJ_hiR : (J : ℝ) ^ 2 < 256 * ((d : ℝ) + 1) := by exact_mod_cast hJ_hi
    have hJp1 : (J : ℝ) + 1 ≤ (17 / 16 : ℝ) * (J : ℝ) := by linarith
    have hJp1_4 : ((J : ℝ) + 1) ^ 4 ≤ ((17 / 16 : ℝ) * (J : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hJp1 4
    have hL2_4 : ((L2 : ℝ) ^ 2) ^ 2 ≤ (J : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hL2R 2
    have hstep1 : ((2 * L2 * (J + 1) : ℝ)) ^ 4 ≤ 16 * (J : ℝ) ^ 2 * ((17 / 16 : ℝ) * (J : ℝ)) ^ 4 := by
      have hid : ((2 * L2 * (J + 1) : ℝ)) ^ 4 = 16 * ((L2 : ℝ) ^ 2) ^ 2 * ((J : ℝ) + 1) ^ 4 := by ring
      rw [hid]
      have h1 : 16 * ((L2 : ℝ) ^ 2) ^ 2 ≤ 16 * (J : ℝ) ^ 2 := by linarith
      exact mul_le_mul h1 hJp1_4 (by positivity) (by positivity)
    have hJ2_pos : 0 < (J : ℝ) ^ 2 := by positivity
    have hJ6_lt : ((J : ℝ) ^ 2) ^ 3 < (256 * ((d : ℝ) + 1)) ^ 3 :=
      pow_lt_pow_left₀ hJ_hiR (le_of_lt hJ2_pos) (by decide : 3 ≠ 0)
    have hid2 : 16 * (J : ℝ) ^ 2 * ((17 / 16 : ℝ) * (J : ℝ)) ^ 4 =
        (289 ^ 2 / 4096 : ℝ) * ((J : ℝ) ^ 2) ^ 3 := by ring
    have hid3 : (289 ^ 2 / 4096 : ℝ) * (256 * ((d : ℝ) + 1)) ^ 3 =
        (136 : ℝ) ^ 4 * ((d : ℝ) + 1) ^ 3 := by ring
    linarith
  · intro J μ step hμJ hJ_eq
    dsimp only
    set M := 2 ^ J + 1
    set ω : ZMod M := (2 : ZMod M) ^ step
    have h2J : (2 : ZMod M) ^ J = -1 := by
      have h0 : ((2 ^ J + 1 : ℕ) : ZMod M) = 0 := ZMod.natCast_self M
      push_cast at h0
      exact eq_neg_of_add_eq_zero_left h0
    have hω_half : ω ^ (2 ^ μ) = -1 := by
      dsimp only [ω]
      rw [← pow_mul, mul_comm step (2 ^ μ), ← hJ_eq, h2J]
    have hω_full : ω ^ (2 ^ (μ + 1)) = 1 := by
      rw [pow_succ, pow_mul, hω_half]
      norm_num
    have hinv : (-(2 : ZMod M) ^ (J - μ)) * ((2 : ZMod M) ^ μ) = 1 := by
      rw [neg_mul, ← pow_add, Nat.sub_add_cancel hμJ, h2J, neg_neg]
    exact ⟨h2J, hω_half, hω_full, hinv⟩
  · intro L1 L2 ω x t1 t2 hωL
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j2 _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j1 _ => ?_
    have hexp : (L2 * j1 + j2) * (t1 + L1 * t2) =
        L1 * j2 * t2 + j2 * t1 + L2 * j1 * t1 + (L1 * L2) * (j1 * t2) := by ring
    rw [hexp, pow_add, pow_add, pow_add, pow_mul ω (L1 * L2) (j1 * t2), hωL, one_pow, mul_one]
    ring
