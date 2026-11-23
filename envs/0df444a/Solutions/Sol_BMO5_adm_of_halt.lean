-- Prove2me | solution 1 for BMO5.adm_of_halt
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T17:44:40.254515+00:00
-- url     : https://prove2.me/submissions/906cee79-0f30-4dc2-9443-7c75577729d6

import Mathlib
import Definitions.Def_BMO5Adm

set_option maxHeartbeats 1000000

namespace BMO5H

theorem lt_pow (x : ℕ) : x < 2 ^ x := by
  induction x with
  | zero => norm_num
  | succ x ih => rw [pow_succ]; omega

theorem bigineq (D i : ℕ) (h : 4 * D + 16 ≤ i) :
    (3:ℤ) ^ D * (3 * (i : ℤ) + 9) < 20 * 2 ^ i + (i : ℤ) + 1 := by
  have h3 : 3 ^ D ≤ 4 ^ D := Nat.pow_le_pow_left (by norm_num) D
  have h4 : (4:ℕ) ^ D = 2 ^ (2 * D) := by rw [pow_mul]; norm_num
  have hsplit : (2:ℕ) ^ i = 2 ^ (2 * D) * 2 ^ (i - 2 * D) := by
    rw [← pow_add]; congr 1; omega
  have hlt := lt_pow (i - 2 * D)
  have key : 3 * i + 9 < 20 * 2 ^ (i - 2 * D) := by omega
  have hpos : 0 < 2 ^ (2 * D) := by positivity
  have hN : 3 ^ D * (3 * i + 9) < 20 * 2 ^ i := by
    calc 3 ^ D * (3 * i + 9) ≤ 2 ^ (2 * D) * (3 * i + 9) :=
          Nat.mul_le_mul_right _ (by rw [← h4]; exact h3)
      _ < 2 ^ (2 * D) * (20 * 2 ^ (i - 2 * D)) := Nat.mul_lt_mul_of_pos_left key hpos
      _ = 20 * 2 ^ i := by rw [hsplit]; ring
  have hN' : 3 ^ D * (3 * i + 9) < 20 * 2 ^ i + i + 1 := by omega
  exact_mod_cast hN'

end BMO5H

theorem solution (a b : ℕ → ℕ) (a_ini : a 0 = 0) (b_ini : b 0 = 5)
    (a_rec : ∀ n, a (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then a n + 1 else a n)
    (b_rec : ∀ n, b (n + 1) = if 10 * 2 ^ (a n) - 1 ≤ b n then b n - (10 * 2 ^ (a n) - 1)
      else 3 * b n + a n + 5) :
    ∀ D, ∃ i0, ∀ n, b n = 10 * 2 ^ (a n) - 2 → i0 ≤ a n → BMO5Adm.adm D (a n) = true := by
  have inv : ∀ n, 2 * b n + a n + 5 < 3 * (20 * 2 ^ (a n) + a n + 3) := by
    intro n
    induction n with
    | zero => rw [a_ini, b_ini]; norm_num
    | succ n ih =>
      have hP : 1 ≤ 2 ^ (a n) := Nat.one_le_two_pow
      by_cases h : 10 * 2 ^ (a n) - 1 ≤ b n
      · rw [a_rec, b_rec, if_pos h, if_pos h, pow_succ]
        generalize 2 ^ (a n) = P at *
        omega
      · rw [a_rec, b_rec, if_neg h, if_neg h]
        generalize 2 ^ (a n) = P at *
        omega
  have sT : ∀ m, ¬ (10 * 2 ^ (a m) - 1 ≤ b m) →
      a (m + 1) = a m ∧ b (m + 1) = 3 * b m + a m + 5 :=
    fun m h => ⟨by rw [a_rec, if_neg h], by rw [b_rec, if_neg h]⟩
  have sS : ∀ m, 10 * 2 ^ (a m) - 1 ≤ b m →
      a (m + 1) = a m + 1 ∧ b (m + 1) = b m - (10 * 2 ^ (a m) - 1) :=
    fun m h => ⟨by rw [a_rec, if_pos h], by rw [b_rec, if_pos h]⟩
  have pw : ∀ m k, a k = a m + 1 → 2 ^ (a k) = 2 * 2 ^ (a m) :=
    fun m k h => by rw [h, pow_succ]; ring
  have P1 : ∀ m, 1 ≤ 2 ^ (a m) := fun m => Nat.one_le_two_pow
  -- backward walk
  have walk : ∀ (i Dt : ℕ), Dt + 2 ≤ i →
      (3:ℤ) ^ Dt * (3 * (i : ℤ) + 9) < 20 * 2 ^ i + (i : ℤ) + 1 →
      ∀ (D p m d : ℕ) (F : ℤ), a p + d = i → F = 3 ^ m * (2 * (b p : ℤ) + a p + 5) →
        20 * 2 ^ i + (i : ℤ) + 1 ≤ F → m + D ≤ Dt → d ≤ m →
        BMO5Adm.okb i D F m d = true := by
    intro i Dt hiD hbig D
    induction D with
    | zero => intro p m d F _ _ _ _ _; simp [BMO5Adm.okb]
    | succ D ih =>
      intro p m d F hlev hF hN hm hd
      have hp0 : p ≠ 0 := by
        rintro rfl; rw [a_ini] at hlev; omega
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      simp only [BMO5Adm.okb, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      by_cases hq : 10 * 2 ^ (a q) - 1 ≤ b q
      · -- subtraction at q
        obtain ⟨ea, eb⟩ := sS q hq
        have hq0 : q ≠ 0 := by
          rintro rfl; rw [a_ini, b_ini] at hq; norm_num at hq
        obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        by_cases hr : 10 * 2 ^ (a r) - 1 ≤ b r
        · -- two subtractions: impossible
          exfalso
          obtain ⟨ea', eb'⟩ := sS r hr
          have hinv := inv r
          have q1 := pw r (r + 1) ea'
          have p0 := P1 r
          have hsmall : 2 * b (r + 1 + 1) + a (r + 1 + 1) + 5 < 3 * a (r + 1 + 1) + 9 := by
            omega
          have hc : 2 * (b (r + 1 + 1) : ℤ) + a (r + 1 + 1) + 5 < 3 * (i : ℤ) + 9 := by
            have : a (r + 1 + 1) ≤ i := by omega
            omega
          have h1 : F < 3 ^ m * (3 * (i : ℤ) + 9) := by
            rw [hF]; exact mul_lt_mul_of_pos_left hc (pow_pos (by norm_num) m)
          have h2 : (3:ℤ) ^ m * (3 * (i : ℤ) + 9) ≤ 3 ^ Dt * (3 * (i : ℤ) + 9) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
          linarith
        · -- tripling at r: an ST block
          obtain ⟨ea', eb'⟩ := sT r hr
          right
          have hid : i - d - 1 = a (r + 1) := by omega
          have p1 := P1 (r + 1)
          have hbN : b (r + 1 + 1) + 10 * 2 ^ (a (r + 1)) = b (r + 1) + 1 := by omega
          have hbZ : (b (r + 1 + 1) : ℤ) = b (r + 1) - 10 * 2 ^ (a (r + 1)) + 1 := by
            have : ((b (r + 1 + 1) + 10 * 2 ^ (a (r + 1)) : ℕ) : ℤ) = ((b (r + 1) + 1 : ℕ) : ℤ) := by
              rw [hbN]
            push_cast at this
            linarith
          have hb1 : (b (r + 1) : ℤ) = 3 * b r + a r + 5 := by exact_mod_cast eb'
          have ha2 : (a (r + 1 + 1) : ℤ) = a (r + 1) + 1 := by exact_mod_cast ea
          have ha1 : (a (r + 1) : ℤ) = a r := by exact_mod_cast ea'
          have hG : F + 3 ^ m * (20 * 2 ^ (i - d - 1) - 3) =
              3 ^ (m + 1) * (2 * (b r : ℤ) + a r + 5) := by
            rw [hF, hid, hbZ, ha2, hb1, ha1]
            ring
          have hnn : (0:ℤ) ≤ 3 ^ m * (20 * 2 ^ (i - d - 1) - 3) := by
            have h2p : (0:ℤ) < 2 ^ (i - d - 1) := pow_pos (by norm_num) _
            exact mul_nonneg (le_of_lt (pow_pos (by norm_num) m)) (by omega)
          refine ⟨by rw [hG]; exact Int.mul_emod_right _ _, ?_⟩
          exact ih r (m + 1) (d + 1) _ (by omega) hG (by linarith) (by omega) (by omega)
      · -- tripling at q: a T block
        obtain ⟨ea, eb⟩ := sT q hq
        left
        have hb1 : (b (q + 1) : ℤ) = 3 * b q + a q + 5 := by exact_mod_cast eb
        have ha1 : (a (q + 1) : ℤ) = a q := by exact_mod_cast ea
        have hF' : F = 3 ^ (m + 1) * (2 * (b q : ℤ) + a q + 5) := by
          rw [hF, hb1, ha1]; ring
        refine ⟨by rw [hF']; exact Int.mul_emod_right _ _, ?_⟩
        exact ih q (m + 1) d F (by omega) hF' hN (by omega) (by omega)
  intro D
  refine ⟨4 * D + 16, fun n hb hn => ?_⟩
  have hbig := BMO5H.bigineq D (a n) hn
  have p := P1 n
  have hbZ : (b n : ℤ) = 10 * 2 ^ (a n) - 2 := by
    have h' : b n + 2 = 10 * 2 ^ (a n) := by omega
    have : ((b n + 2 : ℕ) : ℤ) = ((10 * 2 ^ (a n) : ℕ) : ℤ) := by rw [h']
    push_cast at this
    linarith
  unfold BMO5Adm.adm
  exact walk (a n) D (by omega) hbig D n 0 0 _ (by omega)
    (by rw [hbZ]; ring) le_rfl (by omega) le_rfl
