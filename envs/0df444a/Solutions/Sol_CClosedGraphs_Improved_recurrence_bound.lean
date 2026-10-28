-- Prove2me | solution 1 for CClosedGraphs.Improved.recurrence_bound
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T03:02:50.006695+00:00
-- url     : https://prove2.me/submissions/8a91e150-11bd-4fdb-b21d-71b4aba95519

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace Prove2SwarmSubmission
open _root_.CClosedGraphs.Improved

set_option autoImplicit false

namespace CClosedGraphs.Improved

/-- Coefficient of `m ^ p` in `F0 m c`. -/
private noncomputable def A0 (c : ℕ) : ℝ :=
  (4 : ℝ) ^ ((((c : ℝ) + 4) * ((c : ℝ) - 1)) / 2)

/-- The base-2 factor in the exponent of `F0 m c`. -/
private noncomputable def a0 (c : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 - (c : ℝ))

/-- The exponent `p(c) = 2 - a0 c`. -/
private noncomputable def p0 (c : ℕ) : ℝ := 2 - a0 c

/-- The exponent `q(c) = p(c-1) = 2 - 2*a0 c`. -/
private noncomputable def q0 (c : ℕ) : ℝ := 2 - 2 * a0 c

private lemma a0_pos (c : ℕ) : 0 < a0 c := by
  unfold a0
  exact Real.rpow_pos_of_pos (by norm_num) _

private lemma a0_nonneg (c : ℕ) : 0 ≤ a0 c := (a0_pos c).le

private lemma a0_le_half {c : ℕ} (hc : 2 ≤ c) : a0 c ≤ (1 : ℝ) / 2 := by
  unfold a0
  have hcast : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hexp : 1 - (c : ℝ) ≤ -1 := by linarith
  have hmono : (2 : ℝ) ^ (1 - (c : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    (2 : ℝ) ^ (1 - (c : ℝ)) ≤ (2 : ℝ) ^ (-1 : ℝ) := hmono
    _ = (1 : ℝ) / 2 := by
      rw [Real.rpow_neg_one]
      norm_num

private lemma p0_ge_one {c : ℕ} (hc : 2 ≤ c) : 1 ≤ p0 c := by
  unfold p0
  have h := a0_le_half hc
  linarith

private lemma q0_nonneg {c : ℕ} (hc : 2 ≤ c) : 0 ≤ q0 c := by
  unfold q0
  have h := a0_le_half hc
  linarith

private lemma q0_sub_one (c : ℕ) : q0 c - 1 = 1 - 2 * a0 c := by
  unfold q0
  ring

private lemma p0_sub_one (c : ℕ) : p0 c - 1 = 1 - a0 c := by
  unfold p0
  ring

private lemma a0_pred {c : ℕ} (hc : 1 ≤ c) : a0 (c - 1) = 2 * a0 c := by
  unfold a0
  have hcast : (((c - 1 : ℕ) : ℝ)) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub hc]
    norm_num
  calc
    (2 : ℝ) ^ (1 - (((c - 1 : ℕ) : ℝ)))
        = (2 : ℝ) ^ ((1 - (c : ℝ)) + 1) := by
          congr 1
          rw [hcast]
          ring
    _ = (2 : ℝ) ^ (1 - (c : ℝ)) * (2 : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_add (by norm_num)]
    _ = 2 * a0 c := by
          unfold a0
          norm_num [mul_comm]

private lemma F0_eq (m : ℝ) (c : ℕ) : F0 m c = A0 c * m ^ (p0 c) := by
  unfold F0 A0 p0 a0
  rfl

private lemma F0_pred_eq (m : ℝ) (c : ℕ) (hc : 1 ≤ c) :
    F0 m (c - 1) = A0 (c - 1) * m ^ (q0 c) := by
  unfold F0 A0 q0
  congr 1
  have hp : (2 : ℝ) ^ (1 - (((c - 1 : ℕ) : ℝ))) = 2 * a0 c := a0_pred hc
  rw [hp]

private lemma A0_pos (c : ℕ) : 0 < A0 c := by
  unfold A0
  exact Real.rpow_pos_of_pos (by norm_num) _

private lemma A0_rec {c : ℕ} (hc : 2 ≤ c) :
    A0 c = A0 (c - 1) * (4 : ℝ) ^ ((c : ℝ) + 1) := by
  unfold A0
  have hcast : (((c - 1 : ℕ) : ℝ)) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ c)]
    norm_num
  have hexp : (((c : ℝ) + 4) * ((c : ℝ) - 1)) / 2 =
      (((((c - 1 : ℕ) : ℝ) + 4) * ((((c - 1 : ℕ) : ℝ)) - 1)) / 2) +
        ((c : ℝ) + 1) := by
    rw [hcast]
    ring
  rw [hexp]
  rw [Real.rpow_add (by norm_num)]

private lemma A0_pred_le_A0 {c : ℕ} (hc : 2 ≤ c) : A0 (c - 1) ≤ A0 c := by
  rw [A0_rec hc]
  have hnonneg_exp : 0 ≤ (c : ℝ) + 1 := by positivity
  have hfac : (1 : ℝ) ≤ (4 : ℝ) ^ ((c : ℝ) + 1) :=
    Real.one_le_rpow (by norm_num) hnonneg_exp
  calc
    A0 (c - 1) = A0 (c - 1) * 1 := by ring
    _ ≤ A0 (c - 1) * (4 : ℝ) ^ ((c : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hfac (A0_pos (c - 1)).le

private lemma A0_pred_mul_two_pow_le_A0 {c : ℕ} (hc : 2 ≤ c) :
    A0 (c - 1) * (2 : ℝ) ^ c ≤ A0 c := by
  rw [A0_rec hc]
  have hpow : (2 : ℝ) ^ c ≤ (4 : ℝ) ^ ((c : ℝ) + 1) := by
    have hcast : ((c : ℝ) + 1) = ((c + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, Real.rpow_natCast]
    calc
      (2 : ℝ) ^ c ≤ (4 : ℝ) ^ c := by
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) c
      _ ≤ (4 : ℝ) ^ (c + 1) := by
        exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ c)
  exact mul_le_mul_of_nonneg_left hpow (A0_pos (c - 1)).le

private lemma low_power_bound {n Δ : ℝ} {c : ℕ} (hc : 2 ≤ c)
    (hn : 1 ≤ n) (hΔ0 : 0 < Δ) (hΔsqrt : Δ ≤ Real.sqrt n) :
    n * Δ ^ (q0 c) ≤ n ^ (p0 c) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hΔq : Δ ^ (q0 c) ≤ (Real.sqrt n) ^ (q0 c) :=
    Real.rpow_le_rpow hΔ0.le hΔsqrt (q0_nonneg hc)
  have hsqrtpow : (Real.sqrt n) ^ (q0 c) = n ^ (1 - a0 c) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hnpos.le]
    congr 1
    unfold q0
    ring
  have hnpow : n * n ^ (1 - a0 c) = n ^ (p0 c) := by
    have h := Real.rpow_add hnpos (1 : ℝ) (1 - a0 c)
    simpa [p0, show 1 + (1 - a0 c) = 2 - a0 c by ring, Real.rpow_one] using h.symm
  calc
    n * Δ ^ (q0 c) ≤ n * (Real.sqrt n) ^ (q0 c) :=
      mul_le_mul_of_nonneg_left hΔq hnpos.le
    _ = n * n ^ (1 - a0 c) := by rw [hsqrtpow]
    _ = n ^ (p0 c) := hnpow

private lemma rem_rpow_le {n s p : ℝ} (hs0 : 0 ≤ s) (hsn : s ≤ n)
    (hp : 1 ≤ p) : s ^ p ≤ s * n ^ (p - 1) := by
  rcases eq_or_lt_of_le hs0 with hs | hs
  · subst s
    have hpne : p ≠ 0 := by linarith
    rw [Real.zero_rpow hpne]
    simp
  · have hspow : s ^ p = s * s ^ (p - 1) := by
      have h := Real.rpow_add hs (1 : ℝ) (p - 1)
      simpa [show 1 + (p - 1) = p by ring, Real.rpow_one] using h
    rw [hspow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hs0 hsn (sub_nonneg.mpr hp)) hs0

private lemma high_core {n Δ a : ℝ} (hn : 0 < n) (hΔ : 0 < Δ) (ha : 0 ≤ a)
    (hsqrt : Real.sqrt n < Δ) :
    n * Δ ^ (1 - 2 * a) ≤ Δ * n ^ (1 - a) := by
  have hn_le_sq : n ≤ Δ ^ 2 := le_of_lt (Real.lt_sq_of_sqrt_lt hsqrt)
  have hna : n ^ a ≤ Δ ^ (2 * a) := by
    calc
      n ^ a ≤ (Δ ^ 2) ^ a := Real.rpow_le_rpow hn.le hn_le_sq ha
      _ = Δ ^ (2 * a) := by
        rw [← Real.rpow_natCast Δ 2]
        exact (Real.rpow_mul hΔ.le (2 : ℝ) a).symm
  have hna_pos : 0 < n ^ a := Real.rpow_pos_of_pos hn a
  have hΔ2a_pos : 0 < Δ ^ (2 * a) := Real.rpow_pos_of_pos hΔ (2 * a)
  have hinv : (Δ ^ (2 * a))⁻¹ ≤ (n ^ a)⁻¹ :=
    (inv_le_inv₀ hΔ2a_pos hna_pos).2 hna
  have hneg : Δ ^ (-(2 * a)) ≤ n ^ (-a) := by
    simpa [Real.rpow_neg hΔ.le, Real.rpow_neg hn.le] using hinv
  have hsplit : Δ ^ (1 - 2 * a) = Δ * Δ ^ (-(2 * a)) := by
    have h := Real.rpow_add hΔ (1 : ℝ) (-(2 * a))
    simpa [show 1 + -(2 * a) = 1 - 2 * a by ring, Real.rpow_one] using h
  have hcombine : n * n ^ (-a) = n ^ (1 - a) := by
    have h := Real.rpow_add hn (1 : ℝ) (-a)
    simpa [show 1 + -a = 1 - a by ring, Real.rpow_one] using h.symm
  calc
    n * Δ ^ (1 - 2 * a) = n * (Δ * Δ ^ (-(2 * a))) := by rw [hsplit]
    _ ≤ n * (Δ * n ^ (-a)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hneg hΔ.le) hn.le
    _ = Δ * (n * n ^ (-a)) := by ring
    _ = Δ * n ^ (1 - a) := by rw [hcombine]

private lemma high_power_bound {n Δ : ℝ} {c : ℕ}
    (hn : 1 ≤ n) (hΔ0 : 0 < Δ) (hsqrt : Real.sqrt n < Δ) :
    n * Δ ^ (q0 c - 1) ≤ Δ * n ^ (p0 c - 1) := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcore := high_core hnpos hΔ0 (a0_nonneg c) hsqrt
  rw [q0_sub_one c, p0_sub_one c]
  exact hcore

private lemma high_rpow_div {n Δ : ℝ} {c : ℕ} (hΔ0 : 0 < Δ) :
    Δ ^ (q0 c) * (n / Δ) = n * Δ ^ (q0 c - 1) := by
  have hsub : Δ ^ (q0 c - 1) = Δ ^ (q0 c) / Δ := by
    rw [Real.rpow_sub_one hΔ0.ne']
  rw [hsub]
  field_simp

/-- The exact frozen `recurrence_bound` conjunction. -/
theorem recurrence_bound {c : ℕ} (hc : 2 ≤ c) {n Δ : ℝ} (hn : 1 ≤ n) (hΔ0 : 0 < Δ)
    (hΔn : Δ ≤ n) :
    (Δ ≤ Real.sqrt n → n * F0 Δ (c - 1) ≤ F0 n c) ∧
      (Real.sqrt n < Δ → F0 Δ (c - 1) * (n / Δ) * 2 ^ c + F0 (n - Δ) c ≤ F0 n c) := by
  constructor
  · intro hΔsqrt
    have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
    calc
      n * F0 Δ (c - 1) = A0 (c - 1) * (n * Δ ^ (q0 c)) := by
        rw [F0_pred_eq Δ c (by omega)]
        ring
      _ ≤ A0 (c - 1) * n ^ (p0 c) := by
        exact mul_le_mul_of_nonneg_left (low_power_bound hc hn hΔ0 hΔsqrt) (A0_pos (c - 1)).le
      _ ≤ A0 c * n ^ (p0 c) := by
        exact mul_le_mul_of_nonneg_right (A0_pred_le_A0 hc) (Real.rpow_nonneg hnpos.le _)
      _ = F0 n c := by rw [F0_eq]
  · intro hsqrt
    have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
    have hfirst :
        F0 Δ (c - 1) * (n / Δ) * 2 ^ c ≤ A0 c * (Δ * n ^ (p0 c - 1)) := by
      rw [F0_pred_eq Δ c (by omega)]
      have hdiv : Δ ^ (q0 c) * (n / Δ) = n * Δ ^ (q0 c - 1) := high_rpow_div hΔ0
      have hcoef := A0_pred_mul_two_pow_le_A0 hc
      have hnonneg : 0 ≤ n * Δ ^ (q0 c - 1) :=
        mul_nonneg hnpos.le (Real.rpow_nonneg hΔ0.le _)
      calc
        A0 (c - 1) * Δ ^ (q0 c) * (n / Δ) * (2 : ℝ) ^ c
            = A0 (c - 1) * (Δ ^ (q0 c) * (n / Δ)) * (2 : ℝ) ^ c := by ring
        _ = A0 (c - 1) * (n * Δ ^ (q0 c - 1)) * (2 : ℝ) ^ c := by rw [hdiv]
        _ = (A0 (c - 1) * (2 : ℝ) ^ c) * (n * Δ ^ (q0 c - 1)) := by ring
        _ ≤ A0 c * (n * Δ ^ (q0 c - 1)) :=
              mul_le_mul_of_nonneg_right hcoef hnonneg
        _ ≤ A0 c * (Δ * n ^ (p0 c - 1)) := by
              exact mul_le_mul_of_nonneg_left (high_power_bound hn hΔ0 hsqrt) (A0_pos c).le
    have hrem : (n - Δ) ^ (p0 c) ≤ (n - Δ) * n ^ (p0 c - 1) :=
      rem_rpow_le (sub_nonneg.mpr hΔn) (by linarith) (p0_ge_one hc)
    have hsecond :
        F0 (n - Δ) c ≤ A0 c * ((n - Δ) * n ^ (p0 c - 1)) := by
      rw [F0_eq]
      exact mul_le_mul_of_nonneg_left hrem (A0_pos c).le
    have hsum : Δ * n ^ (p0 c - 1) + (n - Δ) * n ^ (p0 c - 1) =
        n * n ^ (p0 c - 1) := by ring
    have hnpow : n * n ^ (p0 c - 1) = n ^ (p0 c) := by
      have h := Real.rpow_add hnpos (1 : ℝ) (p0 c - 1)
      simpa [show 1 + (p0 c - 1) = p0 c by ring, Real.rpow_one] using h.symm
    calc
      F0 Δ (c - 1) * (n / Δ) * 2 ^ c + F0 (n - Δ) c
          ≤ A0 c * (Δ * n ^ (p0 c - 1)) +
              A0 c * ((n - Δ) * n ^ (p0 c - 1)) := add_le_add hfirst hsecond
      _ = A0 c * (Δ * n ^ (p0 c - 1) + (n - Δ) * n ^ (p0 c - 1)) := by ring
      _ = A0 c * (n * n ^ (p0 c - 1)) := by rw [hsum]
      _ = A0 c * n ^ (p0 c) := by rw [hnpow]
      _ = F0 n c := by rw [F0_eq]

end CClosedGraphs.Improved

end Prove2SwarmSubmission

open CClosedGraphs.Improved
theorem solution {c : ℕ} (hc : 2 ≤ c) {n Δ : ℝ} (hn : 1 ≤ n) (hΔ0 : 0 < Δ)
    (hΔn : Δ ≤ n) :
    (Δ ≤ Real.sqrt n → n * F0 Δ (c - 1) ≤ F0 n c) ∧
      (Real.sqrt n < Δ → F0 Δ (c - 1) * (n / Δ) * 2 ^ c + F0 (n - Δ) c ≤ F0 n c) := by
  exact Prove2SwarmSubmission.CClosedGraphs.Improved.recurrence_bound hc hn hΔ0 hΔn
