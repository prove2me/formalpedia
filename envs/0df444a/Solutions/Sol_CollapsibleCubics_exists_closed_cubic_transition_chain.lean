-- Prove2me | solution 1 for CollapsibleCubics.exists_closed_cubic_transition_chain
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:01:46.084192+00:00
-- url     : https://prove2.me/submissions/ef9b592f-c335-44e6-be92-7a42b9cf5b59

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Polynomial

private lemma no_rat_root_cubic_two_two (r : ℚ) : r ^ 3 + 2 * r + 2 ≠ 0 := by
  intro hr
  set a : ℤ := r.num
  set b : ℕ := r.den
  have hb_pos : 0 < b := r.pos
  have hcop : Nat.Coprime a.natAbs b := r.reduced
  have hb_ne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
  have hr_eq : r = (a : ℚ) / (b : ℚ) := (Rat.num_div_den r).symm
  have hq : (a : ℚ) ^ 3 + 2 * (a : ℚ) * (b : ℚ) ^ 2 + 2 * (b : ℚ) ^ 3 = 0 := by
    have h1 : ((a : ℚ) / (b : ℚ)) ^ 3 + 2 * ((a : ℚ) / (b : ℚ)) + 2 = 0 := by
      rwa [← hr_eq]
    calc (a : ℚ) ^ 3 + 2 * (a : ℚ) * (b : ℚ) ^ 2 + 2 * (b : ℚ) ^ 3
        = (((a : ℚ) / (b : ℚ)) ^ 3 + 2 * ((a : ℚ) / (b : ℚ)) + 2) * (b : ℚ) ^ 3 := by
            field_simp
      _ = 0 := by rw [h1, zero_mul]
  have hab : a ^ 3 + 2 * a * (b : ℤ) ^ 2 + 2 * (b : ℤ) ^ 3 = 0 := by
    exact_mod_cast hq
  have ha_even : ∃ k : ℤ, a = 2 * k := by
    refine ⟨a / 2, ?_⟩
    have hmod : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · omega
    · exfalso
      set k : ℤ := a / 2
      have hk : a = 2 * k + 1 := by omega
      have hodd : 2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k + (2 * k + 1) * (b : ℤ) ^ 2 +
          (b : ℤ) ^ 3) + 1 = 0 := by
        rw [hk] at hab
        linarith [show (2 * k + 1) ^ 3 + 2 * (2 * k + 1) * (b : ℤ) ^ 2 + 2 * (b : ℤ) ^ 3 =
          2 * (4 * k ^ 3 + 6 * k ^ 2 + 3 * k + (2 * k + 1) * (b : ℤ) ^ 2 + (b : ℤ) ^ 3) + 1 by
          ring]
      omega
  obtain ⟨k, hk⟩ := ha_even
  rw [hk] at hab hcop
  have hb_even : 2 ∣ b := by
    refine ⟨b / 2, ?_⟩
    have hmod : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hmod with h0 | h1
    · omega
    · exfalso
      set m : ℕ := b / 2
      have hm : (b : ℤ) = 2 * (m : ℤ) + 1 := by omega
      have hmod4 : 4 * (2 * k ^ 3 + k * (2 * (m : ℤ) + 1) ^ 2 + 4 * (m : ℤ) ^ 3 +
          6 * (m : ℤ) ^ 2 + 3 * (m : ℤ)) + 2 = 0 := by
        rw [hm] at hab
        linarith [show (2 * k) ^ 3 + 2 * (2 * k) * (2 * (m : ℤ) + 1) ^ 2 +
          2 * (2 * (m : ℤ) + 1) ^ 3 =
          4 * (2 * k ^ 3 + k * (2 * (m : ℤ) + 1) ^ 2 + 4 * (m : ℤ) ^ 3 +
            6 * (m : ℤ) ^ 2 + 3 * (m : ℤ)) + 2 by ring]
      omega
  have ha_dvd : 2 ∣ (2 * k).natAbs := by
    rw [Int.natAbs_mul]
    exact dvd_mul_right 2 k.natAbs
  have hg : 2 ∣ Nat.gcd (2 * k).natAbs b := Nat.dvd_gcd ha_dvd hb_even
  rw [hcop.gcd_eq_one] at hg
  omega

private lemma irreducible_cubic_two_two :
    Irreducible (X ^ 3 + C (2 : ℚ) * X + C (2 : ℚ) : ℚ[X]) := by
  set p : ℚ[X] := X ^ 3 + C (2 : ℚ) * X + C (2 : ℚ)
  have hp_deg : p.natDegree = 3 := by
    dsimp [p]
    rw [natDegree_add_C, natDegree_add_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow 3
    · rw [natDegree_C_mul_X 2 (by norm_num), natDegree_X_pow 3]
      omega
  have hp0 : p ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hp_deg
    omega
  have hpu : ¬ IsUnit p := by
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    omega
  rw [irreducible_iff_lt_natDegree_lt hp0 hpu]
  intro q _ hqd hdvd
  rw [hp_deg, Finset.mem_Ioc] at hqd
  have hq1 : q.natDegree = 1 := by omega
  have hq_deg : q.degree = 1 := degree_eq_iff_natDegree_eq_of_pos zero_lt_one |>.mpr hq1
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hq_deg
  obtain ⟨s, hs⟩ := hdvd
  have hpr : p.eval r = 0 := by
    rw [hs, eval_mul, hr.eq_zero, zero_mul]
  have hp_eval : p.eval r = r ^ 3 + 2 * r + 2 := by
    simp [p]
  exact no_rat_root_cubic_two_two r (hp_eval ▸ hpr)

private def cubicLyapunov (t : ℚ) : ℚ :=
  t ^ 4 + 4 * t ^ 2 + 8 * t

private lemma step_decreases {t x y : ℚ}
    (htrans : (t ^ 2 + t * x + x ^ 2 + 2) * y = t ^ 2 * x + t * x ^ 2 - 2) :
    cubicLyapunov y < cubicLyapunov t := by
  set D : ℚ := t ^ 2 + t * x + x ^ 2 + 2
  set q : ℚ := t ^ 3 + 2 * t + 2
  set k : ℚ := (x + t / 2) ^ 2
  set E : ℚ :=
    4 * k ^ 3 + (3 * t ^ 2 + 20) * k ^ 2 +
    (7 / 4 * t ^ 4 + (2 * t + 2) ^ 2 + 10 * t ^ 2 + 28) * k +
    5 / 16 * t ^ 6 + 9 / 4 * t ^ 4 + (t ^ 2 + t) ^ 2 +
    (2 * t + 2) ^ 2 + 7 * t ^ 2 + 8
  have hD_pos : 0 < D := by
    have hD_eq : D = k + 3 / 4 * t ^ 2 + 2 := by
      dsimp [D, k]; ring
    rw [hD_eq]
    positivity
  have hq_ne : q ≠ 0 := no_rat_root_cubic_two_two t
  have hE_pos : 0 < E := by
    dsimp [E, k]
    positivity
  have hDy : D * y = D * t - q := by
    have hsub : D * t - (t ^ 2 * x + t * x ^ 2 - 2) = q := by
      dsimp [D, q]; ring
    linarith [htrans, hsub]
  have hident : D ^ 4 * (cubicLyapunov t - cubicLyapunov y) = q ^ 2 * E := by
    calc D ^ 4 * (cubicLyapunov t - cubicLyapunov y)
        = D ^ 4 * cubicLyapunov t -
            ((D * y) ^ 4 + 4 * D ^ 2 * (D * y) ^ 2 + 8 * D ^ 3 * (D * y)) := by
            dsimp [cubicLyapunov]; ring
      _ = D ^ 4 * cubicLyapunov t -
            ((D * t - q) ^ 4 + 4 * D ^ 2 * (D * t - q) ^ 2 + 8 * D ^ 3 * (D * t - q)) := by
            rw [hDy]
      _ = q ^ 2 * E := by
            dsimp [cubicLyapunov, D, q, E, k]; ring
  have hprod_pos : 0 < D ^ 4 * (cubicLyapunov t - cubicLyapunov y) := by
    rw [hident]
    exact mul_pos (sq_pos_of_ne_zero hq_ne) hE_pos
  have hD4_pos : 0 < D ^ 4 := pow_pos hD_pos 4
  have hdiff_pos : 0 < cubicLyapunov t - cubicLyapunov y :=
    pos_of_mul_pos_right hprod_pos hD4_pos.le
  linarith

theorem solution :
    ¬ (∀ (d e : ℚ),
        Irreducible (X ^ 3 + C d * X + C e : ℚ[X]) →
        (¬ ∃ r s : ℚ, r ^ 2 + r * s + s ^ 2 = -d) →
        ∃ n : ℕ, 0 < n ∧ ∃ t x : ℕ → ℚ,
          t n = t 0 ∧ ∀ i < n,
            (t i ^ 2 + t i * x i + x i ^ 2 + d) * t (i + 1) =
              t i ^ 2 * x i + t i * x i ^ 2 - e) := by
  intro hAll
  have hrep2 : ¬ ∃ r s : ℚ, r ^ 2 + r * s + s ^ 2 = -(2 : ℚ) := by
    rintro ⟨r, s, hrs⟩
    nlinarith [sq_nonneg (r + s), sq_nonneg r, sq_nonneg s]
  obtain ⟨n, hn, t, x, hclosed, hstep⟩ := hAll 2 2 irreducible_cubic_two_two hrep2
  have hlt : ∀ m, 0 < m → m ≤ n → cubicLyapunov (t m) < cubicLyapunov (t 0) := by
    intro m hm hmn
    induction m with
    | zero => omega
    | succ k ih =>
      have hk_step := step_decreases (hstep k (Nat.lt_of_succ_le hmn))
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · exact hk_step
      · exact hk_step.trans (ih hk_pos (Nat.le_of_succ_le hmn))
  have hcontra := hlt n hn le_rfl
  rw [hclosed] at hcontra
  exact lt_irrefl _ hcontra
