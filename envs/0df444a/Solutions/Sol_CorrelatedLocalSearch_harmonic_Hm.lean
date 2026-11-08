-- Prove2me | solution 1 for CorrelatedLocalSearch.harmonic_Hm
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:21:03.244946+00:00
-- url     : https://prove2.me/submissions/99780b97-a47c-4da6-9901-6022f5094b70

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_Hm

set_option autoImplicit false

open CorrelatedLocalSearch in
theorem solution (k r : ℕ) (hk : k < 2 * r) (hr : r < k) (m : ℕ) (hm : 1 ≤ m) :
    (∀ d₁ d₂ : ℕ, d₁ < d₂ → d₂ ≤ m → Hm k r m d₁ < Hm k r m d₂) ∧
      Hm k r m 0 = 0 ∧ Hm k r m m = 1 ∧
      ∀ d : ℕ, 1 ≤ d → d < m →
        (r : ℝ) * (k : ℝ) ^ (-sStar k r) * Hm k r m (d - 1) +
            ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) * Hm k r m (d + 1) = Hm k r m d := by
  have hrk : (r : ℝ) < k := by exact_mod_cast hr
  have hkr : (k : ℝ) < 2 * r := by exact_mod_cast hk
  have hq : (0 : ℝ) < (k : ℝ) - r := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hk1 : (1 : ℝ) < k := by
    have : 2 ≤ k := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨q, hqd⟩ : ∃ q, q = (k : ℝ) - r := ⟨_, rfl⟩
  rw [← hqd] at hq
  obtain ⟨L, hLd⟩ : ∃ L, L = lam k r := ⟨_, rfl⟩
  have hL : L = Real.sqrt ((r : ℝ) / q) := by rw [hLd, lam, hqd]
  have hL0 : 0 < L := by rw [hL]; exact Real.sqrt_pos.mpr (div_pos hr0 hq)
  have hL2 : L ^ 2 = (r : ℝ) / q := by rw [hL]; exact Real.sq_sqrt (div_pos hr0 hq).le
  have hL1 : 1 < L := by
    rw [hL, Real.lt_sqrt zero_le_one, one_pow, one_lt_div hq]
    linarith
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt ((r : ℝ) * q) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsd]; exact Real.sqrt_pos.mpr (mul_pos hr0 hq)
  have hs2 : s ^ 2 = (r : ℝ) * q := by rw [hsd]; exact Real.sq_sqrt (mul_pos hr0 hq).le
  have hqL : q * L = s := by
    rw [← sq_eq_sq₀ (mul_pos hq hL0).le hs0.le, mul_pow, hL2, hs2]
    field_simp
  have hrs : (r : ℝ) = s * L := by
    rw [← hqL, mul_assoc, ← sq, hL2]; field_simp
  have hks : (k : ℝ) ^ (-sStar k r) = 1 / (2 * s) := by
    rw [Real.rpow_neg hk0.le, sStar, Real.rpow_logb hk0 hk1.ne', one_div, ← hqd, ← hsd]
    · positivity
  have hHm : ∀ d, Hm k r m d = ((d : ℝ) / m) * L ^ ((d : ℤ) - m) := by
    intro d; rw [Hm, hLd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d₁ d₂ h12 h2m
    rw [hHm, hHm]
    have e1 : L ^ ((d₁ : ℤ) - m) < L ^ ((d₂ : ℤ) - m) := zpow_lt_zpow_right₀ hL1 (by omega)
    have hd2 : (0 : ℝ) < d₂ := by
      have : 0 < d₂ := by omega
      exact_mod_cast this
    have hd12 : (d₁ : ℝ) ≤ d₂ := by exact_mod_cast h12.le
    calc ((d₁ : ℝ) / m) * L ^ ((d₁ : ℤ) - m) ≤ ((d₂ : ℝ) / m) * L ^ ((d₁ : ℤ) - m) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hd12 hm0.le)
            (zpow_pos hL0 _).le
      _ < ((d₂ : ℝ) / m) * L ^ ((d₂ : ℤ) - m) := mul_lt_mul_of_pos_left e1 (div_pos hd2 hm0)
  · rw [hHm]; simp
  · rw [hHm]; simp [hm0.ne']
  · intro d hd1 hdm
    rw [hHm, hHm, hHm, hks, ← hqd]
    have c1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd1]; simp
    have c2 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by rw [Nat.cast_sub hd1]; simp
    have z1 : L ^ ((d : ℤ) - 1 - m) = L ^ ((d : ℤ) - m) * L⁻¹ := by
      rw [show (d : ℤ) - 1 - m = ((d : ℤ) - m) - 1 by ring, zpow_sub_one₀ hL0.ne']
    have z2 : L ^ (((d + 1 : ℕ) : ℤ) - m) = L ^ ((d : ℤ) - m) * L := by
      rw [show ((d + 1 : ℕ) : ℤ) - m = ((d : ℤ) - m) + 1 by push_cast; ring,
        zpow_add_one₀ hL0.ne']
    rw [c1, c2, z1, z2]
    obtain ⟨e, he⟩ : ∃ e, e = L ^ ((d : ℤ) - m) := ⟨_, rfl⟩
    rw [← he]
    have t1 : (r : ℝ) * (1 / (2 * s)) * (((d : ℝ) - 1) / m * (e * L⁻¹)) =
        ((d : ℝ) - 1) * e / (2 * m) := by
      rw [hrs]; field_simp
    have t2 : q * (1 / (2 * s)) * (((d + 1 : ℕ) : ℝ) / m * (e * L)) =
        ((d : ℝ) + 1) * e / (2 * m) := by
      rw [← hqL]; push_cast; field_simp
    rw [t1, t2]; ring
