-- Prove2me | solution 1 for FourExp.construction_count_1973
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T19:40:54.727755+00:00
-- url     : https://prove2.me/submissions/90439cea-596f-4943-941f-692136698642

import Mathlib

namespace FourExpCount

/-- The counting inequality, as pure algebra. `S`, `t₁`, `t₂`, `d`, `T` stand for the
floor quantities, and `W` for `X(Y₁+Y₂)`. -/
lemma count_core (N q S t₁ t₂ d T W : ℝ) (hW : 0 ≤ W) (hq : 40 * (1 + 28 * W) ≤ q)
    (hqN : q ^ 2 ≤ N) (hN : 84 ≤ N) (hS1 : S * q ≤ N ^ 2) (hS2 : N ^ 2 ≤ (S + 1) * q)
    (hSone : 1 ≤ S) (ht1 : N - q ≤ q * t₁) (ht2 : N * q - 1 ≤ t₂) (ht1n : 0 ≤ t₁)
    (ht2n : 0 ≤ t₂) (hd : S - 1 ≤ 2 * d) (hdn : 0 ≤ d) (hTn : 0 ≤ T)
    (hT : T * q ^ 2 ≤ 40 * (1 + 28 * W) * N ^ 4) :
    80 * N ^ 2 * S + T ≤ 196 * (t₁ * t₂ * d) := by
  have hq7 : (7:ℝ) ≤ q := by nlinarith
  have hqpos : (0:ℝ) < q := by linarith
  have hNpos : (0:ℝ) < N := by linarith
  have hqle : q ≤ N := by nlinarith
  -- the product of the two grid sizes
  have hNq1 : (0:ℝ) ≤ N * q - 1 := by nlinarith
  have hP1 : (N - q) * (N * q - 1) ≤ q * t₁ * t₂ :=
    mul_le_mul ht1 ht2 hNq1 (by nlinarith)
  -- the polynomial comparison
  have hP2 : 82 * N ^ 2 * q ≤ 98 * ((N - q) * (N * q - 1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hqN (by positivity : (0:ℝ) ≤ 98 * N),
      sq_nonneg (N - q), mul_pos hNpos hqpos]
  -- the slack that absorbs the second term
  have hstep6 : T + 82 * N ^ 2 ≤ 2 * N ^ 2 * S := by
    have h1 : T * q ^ 2 ≤ q * N ^ 4 := by
      have := mul_le_mul_of_nonneg_right hq (by positivity : (0:ℝ) ≤ N ^ 4)
      nlinarith
    have h2 : 2 * N ^ 2 * (N ^ 2 - q) ≤ 2 * N ^ 2 * (S * q) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    have h3 : 84 * q ≤ N ^ 2 := by nlinarith
    have h4 : T * q ^ 2 + 82 * N ^ 2 * q ^ 2 ≤ 2 * N ^ 2 * S * q ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ N ^ 2 * q)]
    have hq2 : (0:ℝ) < q ^ 2 := by positivity
    nlinarith
  -- chain everything through one factor of `q`
  have hchain : q * (80 * N ^ 2 * S + T) ≤ q * (196 * (t₁ * t₂ * d)) := by
    have e1 : 98 * (t₁ * t₂) * (S - 1) ≤ 196 * (t₁ * t₂ * d) := by
      have := mul_le_mul_of_nonneg_left hd (by positivity : (0:ℝ) ≤ 98 * (t₁ * t₂))
      nlinarith
    have e2 : 98 * ((N - q) * (N * q - 1)) * (S - 1) ≤ q * (98 * (t₁ * t₂) * (S - 1)) := by
      have h := mul_le_mul_of_nonneg_right hP1 (by linarith : (0:ℝ) ≤ 98 * (S - 1))
      nlinarith
    have e3 : 82 * N ^ 2 * q * (S - 1) ≤ 98 * ((N - q) * (N * q - 1)) * (S - 1) := by
      have := mul_le_mul_of_nonneg_right hP2 (by linarith : (0:ℝ) ≤ S - 1)
      nlinarith
    have e4 : q * (80 * N ^ 2 * S + T) ≤ 82 * N ^ 2 * q * (S - 1) := by
      have := mul_le_mul_of_nonneg_left hstep6 hqpos.le
      nlinarith
    calc q * (80 * N ^ 2 * S + T) ≤ 82 * N ^ 2 * q * (S - 1) := e4
      _ ≤ 98 * ((N - q) * (N * q - 1)) * (S - 1) := e3
      _ ≤ q * (98 * (t₁ * t₂) * (S - 1)) := e2
      _ ≤ q * (196 * (t₁ * t₂ * d)) := by
          exact mul_le_mul_of_nonneg_left e1 hqpos.le
  exact le_of_mul_le_mul_left hchain hqpos

open Real in
lemma rpow_U_le {U : ℕ} {N : ℝ} (hN : 2 ≤ N) (hU : (U : ℝ) ≤ N ^ (20:ℕ)) :
    ((U : ℝ)) ^ (1 / 20 : ℝ) ≤ N := by
  have hNpos : (0:ℝ) < N := by linarith
  calc ((U : ℝ)) ^ (1 / 20 : ℝ) ≤ (N ^ (20:ℕ)) ^ (1 / 20 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hU (by norm_num)
    _ = N := by
        rw [← Real.rpow_natCast N 20, ← Real.rpow_mul hNpos.le]
        norm_num

lemma nat_div_two_ge (S : ℕ) : (S : ℝ) - 1 ≤ 2 * ((S / 2 : ℕ) : ℝ) := by
  have h : S ≤ 2 * (S / 2) + 1 := by omega
  have : (S : ℝ) ≤ 2 * ((S / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h
  linarith

lemma q_facts (N : ℕ) (hN : 84 ≤ N) :
    1 ≤ Real.sqrt (Real.log (N:ℝ)) ∧ Real.sqrt (Real.log (N:ℝ)) ^ 2 ≤ (N:ℝ) ∧
      0 < Real.log (N:ℝ) ∧ Real.sqrt (Real.log (N:ℝ)) ≤ (N:ℝ) ∧
      Real.sqrt (Real.log (N:ℝ)) * Real.sqrt (Real.log (N:ℝ)) = Real.log (N:ℝ) := by
  have hNr : (84:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlog : 1 ≤ Real.log (N:ℝ) := by
    rw [show (1:ℝ) = Real.log (Real.exp 1) by simp]
    refine (Real.log_le_log (Real.exp_pos 1) ?_)
    have := Real.exp_one_lt_d9; linarith
  have hqq : Real.sqrt (Real.log (N:ℝ)) * Real.sqrt (Real.log (N:ℝ)) = Real.log (N:ℝ) :=
    Real.mul_self_sqrt (by linarith)
  have hq1 : 1 ≤ Real.sqrt (Real.log (N:ℝ)) := Real.one_le_sqrt.2 hlog
  have hlogle : Real.log (N:ℝ) ≤ (N:ℝ) := by
    have := Real.log_le_sub_one_of_pos hNpos; linarith
  refine ⟨hq1, ?_, by linarith, ?_, hqq⟩
  · rw [sq, hqq]; exact hlogle
  · nlinarith

lemma S_facts (N : ℕ) (hN : 84 ≤ N) :
    (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) * Real.sqrt (Real.log (N:ℝ)) ≤ (N:ℝ) ^ 2 ∧
      (N:ℝ) ^ 2 ≤ ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) + 1) * Real.sqrt (Real.log (N:ℝ)) ∧
      1 ≤ (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ∧
      (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ≤ (N:ℝ) ^ 2 := by
  obtain ⟨hq1, hq2, hlogpos, hqN, hqq⟩ := q_facts N hN
  have hNr : (84:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hqpos : (0:ℝ) < Real.sqrt (Real.log (N:ℝ)) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← le_div_iff₀ hqpos]; exact Nat.floor_le (by positivity)
  · rw [← div_le_iff₀ hqpos]
    exact (Nat.lt_floor_add_one ((N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ)))).le
  · have h : 1 ≤ ⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ := by
      refine (Nat.one_le_floor_iff _).2 ?_
      rw [le_div_iff₀ hqpos]; nlinarith
    exact_mod_cast h
  · refine (Nat.floor_le (by positivity)).trans ?_
    rw [div_le_iff₀ hqpos]; nlinarith

lemma t_facts (N : ℕ) (hN : 84 ≤ N) :
    (N:ℝ) - Real.sqrt (Real.log (N:ℝ))
        ≤ Real.sqrt (Real.log (N:ℝ)) * (⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ∧
      (N:ℝ) * Real.sqrt (Real.log (N:ℝ)) - 1 ≤ (⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ∧
      (⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ≤ (N:ℝ) ∧
      (⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ≤ (N:ℝ) ^ 2 := by
  obtain ⟨hq1, hq2, hlogpos, hqN, hqq⟩ := q_facts N hN
  have hNr : (84:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hqpos : (0:ℝ) < Real.sqrt (Real.log (N:ℝ)) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := (Nat.lt_floor_add_one ((N:ℝ) / Real.sqrt (Real.log (N:ℝ)))).le
    rw [div_le_iff₀ hqpos] at h
    nlinarith
  · have := (Nat.lt_floor_add_one ((N:ℝ) * Real.sqrt (Real.log (N:ℝ)))).le
    linarith
  · refine (Nat.floor_le (by positivity)).trans ?_
    rw [div_le_iff₀ hqpos]; nlinarith
  · refine (Nat.floor_le (by positivity)).trans ?_
    nlinarith

lemma U_facts (N : ℕ) (hN : 84 ≤ N) :
    ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)
        = 4 * (N:ℝ) ^ 2 * (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ∧
      (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ) ≤ (N:ℝ) ∧
      2 * Real.log (N:ℝ)
        ≤ Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) := by
  obtain ⟨hq1, hq2, hlogpos, hqN, hqq⟩ := q_facts N hN
  obtain ⟨hS1, hS2, hSone, hSN2⟩ := S_facts N hN
  have hNr : (84:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hUeq : ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)
      = 4 * (N:ℝ) ^ 2 * (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) := by push_cast; ring
  have hUN2 : (N:ℝ) ^ 2 ≤ ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ) := by
    rw [hUeq]; nlinarith
  refine ⟨hUeq, ?_, ?_⟩
  · refine rpow_U_le (by linarith) ?_
    rw [hUeq]
    have h4 : 4 * (N:ℝ) ^ 2 * (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) ≤ 4 * (N:ℝ) ^ 4 := by
      nlinarith [sq_nonneg (N:ℝ)]
    have h5 : 4 * (N:ℝ) ^ 4 ≤ (N:ℝ) ^ 5 := by nlinarith [pow_nonneg hNpos.le 4]
    have h20 : (N:ℝ) ^ 5 ≤ (N:ℝ) ^ (20:ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  · have h1 : Real.log ((N:ℝ) ^ 2)
        ≤ Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) hUN2
    rwa [Real.log_pow] at h1

lemma Z_bound (N : ℕ) (X Y₁ Y₂ : ℝ) (hX : 0 ≤ X) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) (hN : 84 ≤ N) :
    ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
        + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X)
      ≤ 28 * (N:ℝ) ^ 3 * (X * (Y₁ + Y₂)) := by
  obtain ⟨ht1, ht2, ht1u, ht2u⟩ := t_facts N hN
  have hNr : (84:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have e1 : (((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) ≤ 14 * (N:ℝ) ^ 2 := by
    push_cast; nlinarith
  have e2 : (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) ≤ 14 * (N:ℝ) ^ 2 := by
    push_cast; nlinarith
  have e3 : ((((2 * N) : ℕ) : ℝ) * X) = 2 * (N:ℝ) * X := by push_cast; ring
  rw [e3]
  have hsum : (((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
      + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂
      ≤ 14 * (N:ℝ) ^ 2 * Y₁ + 14 * (N:ℝ) ^ 2 * Y₂ := by
    have a1 := mul_le_mul_of_nonneg_right e1 hY₁
    have a2 := mul_le_mul_of_nonneg_right e2 hY₂
    linarith
  have h1 : (0:ℝ) ≤ 2 * (N:ℝ) * X := by positivity
  calc ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
        + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * (2 * (N:ℝ) * X)
      ≤ (14 * (N:ℝ) ^ 2 * Y₁ + 14 * (N:ℝ) ^ 2 * Y₂) * (2 * (N:ℝ) * X) :=
        mul_le_mul_of_nonneg_right hsum h1
    _ = 28 * (N:ℝ) ^ 3 * (X * (Y₁ + Y₂)) := by ring

lemma T_bound (L u Z W N : ℝ) (hN : 84 ≤ N) (hL : 2 * Real.log N ≤ L) (hu : u ≤ N) (hu0 : 0 ≤ u)
    (hZ : Z ≤ 28 * N ^ 3 * W) (hZ0 : 0 ≤ Z) (hW : 0 ≤ W) (hlogN : 0 < Real.log N) :
    2 * (1 + u) / ((1 / 20 : ℝ) * L) * (1 + Z) * Real.log N ≤ 40 * (1 + 28 * W) * N ^ 4 := by
  have hLpos : 0 < L := by linarith
  have hA : 2 * (1 + u) / ((1 / 20 : ℝ) * L) * Real.log N ≤ 40 * N := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  calc 2 * (1 + u) / ((1 / 20 : ℝ) * L) * (1 + Z) * Real.log N
      = (2 * (1 + u) / ((1 / 20 : ℝ) * L) * Real.log N) * (1 + Z) := by ring
    _ ≤ (40 * N) * (1 + Z) := mul_le_mul_of_nonneg_right hA (by linarith)
    _ ≤ (40 * N) * (1 + 28 * N ^ 3 * W) := by nlinarith
    _ ≤ 40 * (1 + 28 * W) * N ^ 4 := by
        have hN4 : N ≤ N ^ 4 := by
          calc N = N ^ 1 := by ring
            _ ≤ N ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
        nlinarith [hN4]

end FourExpCount

theorem solution (X Y₁ Y₂ : ℝ) (hX : 0 ≤ X) (hY₁ : 0 ≤ Y₁) (hY₂ : 0 ≤ Y₂) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ((((⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ) / (1 / 20 : ℝ)
              + 2 * (1 + (((⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ) ^ (1 / 20 : ℝ)) / ((1 / 20 : ℝ) * Real.log ((((⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊) * (2 * N) * (2 * N) : ℕ) : ℝ)))
                * (1 + (((14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) : ℕ) * Y₁ + ((14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊) : ℕ) * Y₂) * (((2 * N) : ℕ) * X))
            ≤ ((((14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊)) * ((14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊)) * (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2) : ℕ) : ℝ)) := by
  classical
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = X * (Y₁ + Y₂) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  refine ⟨max 84 ⌈Real.exp ((40 * (1 + 28 * W)) ^ 2)⌉₊, fun N hN => ?_⟩
  have hN84 : 84 ≤ N := by omega
  have hN84r : (84:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN84
  obtain ⟨hq1, hq2, hlogpos, hqN, hqq⟩ := FourExpCount.q_facts N hN84
  obtain ⟨hS1, hS2, hSone, hSN2⟩ := FourExpCount.S_facts N hN84
  obtain ⟨ht1, ht2, ht1u, ht2u⟩ := FourExpCount.t_facts N hN84
  obtain ⟨hUeq, hrp, hlogU⟩ := FourExpCount.U_facts N hN84
  have hZ := FourExpCount.Z_bound N X Y₁ Y₂ hX hY₁ hY₂ hN84
  rw [← hWdef] at hZ
  have hQ : 40 * (1 + 28 * W) ≤ Real.sqrt (Real.log (N:ℝ)) := by
    have hbig : Real.exp ((40 * (1 + 28 * W)) ^ 2) ≤ (N:ℝ) := by
      have h1 := Nat.le_ceil (Real.exp ((40 * (1 + 28 * W)) ^ 2))
      have h2 : ⌈Real.exp ((40 * (1 + 28 * W)) ^ 2)⌉₊ ≤ N := by omega
      have h3 : (⌈Real.exp ((40 * (1 + 28 * W)) ^ 2)⌉₊ : ℝ) ≤ (N:ℝ) := by exact_mod_cast h2
      linarith
    have hlogbig : (40 * (1 + 28 * W)) ^ 2 ≤ Real.log (N:ℝ) := by
      rw [← Real.log_exp ((40 * (1 + 28 * W)) ^ 2)]
      exact Real.log_le_log (Real.exp_pos _) hbig
    rw [show (40 * (1 + 28 * W) : ℝ) = Real.sqrt ((40 * (1 + 28 * W)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hlogbig
  have hZ0 : (0:ℝ) ≤ ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
      + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X) := by
    have h1 : (0:ℝ) ≤ (((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ (((2 * N) : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_nonneg h1 hY₁
    have := mul_nonneg h2 hY₂
    have := mul_nonneg h3 hX
    positivity
  have hrp0 : (0:ℝ) ≤ (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hTq := FourExpCount.T_bound
    (Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)))
    ((((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ))
    (((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
      + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X))
    W (N:ℝ) hN84r hlogU hrp hrp0 hZ hZ0 hW0 hlogpos
  have hTn : (0:ℝ) ≤ 2 * (1 + (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ))
      / ((1 / 20 : ℝ) * Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)))
      * (1 + ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
        + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X)) := by
    have hL : (0:ℝ) < Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) := by
      linarith
    positivity
  have hTq' : (2 * (1 + (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ))
      / ((1 / 20 : ℝ) * Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)))
      * (1 + ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
        + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X)))
      * Real.sqrt (Real.log (N:ℝ)) ^ 2 ≤ 40 * (1 + 28 * W) * (N:ℝ) ^ 4 := by
    rw [show Real.sqrt (Real.log (N:ℝ)) ^ 2 = Real.log (N:ℝ) from by rw [sq, hqq]]
    exact hTq
  have key := FourExpCount.count_core (N:ℝ) (Real.sqrt (Real.log (N:ℝ)))
    (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ)
    (⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ)
    (⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ)
    ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ / 2 : ℕ) : ℝ)
    (2 * (1 + (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ))
      / ((1 / 20 : ℝ) * Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)))
      * (1 + ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
        + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X)))
    W hW0 hQ hq2 hN84r hS1 hS2 hSone ht1 ht2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (FourExpCount.nat_div_two_ge _) (Nat.cast_nonneg _) hTn hTq'
  calc ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ) / (1 / 20 : ℝ)
        + 2 * (1 + (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ))
          / ((1 / 20 : ℝ) * Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)))
          * (1 + ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
            + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X))
      = 80 * (N:ℝ) ^ 2 * (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ)
        + 2 * (1 + (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)) ^ (1 / 20 : ℝ))
          / ((1 / 20 : ℝ) * Real.log (((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ * (2 * N) * (2 * N) : ℕ) : ℝ)))
          * (1 + ((((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₁
            + (((14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊) : ℕ) : ℝ) * Y₂) * ((((2 * N) : ℕ) : ℝ) * X)) := by
        rw [hUeq]; ring
    _ ≤ 196 * ((⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ) * (⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊ : ℝ)
        * ((⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ / 2 : ℕ) : ℝ)) := key
    _ = (((14 * ⌊(N:ℝ) / Real.sqrt (Real.log (N:ℝ))⌋₊) * (14 * ⌊(N:ℝ) * Real.sqrt (Real.log (N:ℝ))⌋₊)
        * (⌊(N:ℝ) ^ 2 / Real.sqrt (Real.log (N:ℝ))⌋₊ / 2) : ℕ) : ℝ) := by push_cast; ring
