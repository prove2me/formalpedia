-- Prove2me | solution 1 for ChenWhitt93.Reflection.colNorm_geometric_series_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:50:09.82634+00:00
-- url     : https://prove2.me/submissions/dfce9c74-4466-4211-8801-3edbf58fcd09

import Mathlib

open Filter Topology Matrix

namespace CexChenWhitt2c2c

/-- A nonnegative submultiplicative "norm" on 1x1 matrices with `normM 1 = 2`. -/
noncomputable def nm (A : Matrix (Fin 1) (Fin 1) ℝ) : ℝ := 2 * |A 0 0|

theorem nm_sub (A B : Matrix (Fin 1) (Fin 1) ℝ) : nm (A * B) ≤ nm A * nm B := by
  unfold nm
  rw [Matrix.mul_apply, Fin.sum_univ_one, abs_mul]
  have ha := abs_nonneg (A 0 0)
  have hb := abs_nonneg (B 0 0)
  nlinarith [mul_nonneg ha hb]

theorem nm_nonneg (A : Matrix (Fin 1) (Fin 1) ℝ) : 0 ≤ nm A := by
  unfold nm; positivity

theorem nm_pow (k : ℕ) : nm ((0 : Matrix (Fin 1) (Fin 1) ℝ) ^ k) = if k = 0 then 2 else 0 := by
  rcases k with _ | k
  · simp [nm]
  · simp [nm, zero_pow (Nat.succ_ne_zero k)]

theorem tsum_nm : (∑' k : ℕ, nm ((0 : Matrix (Fin 1) (Fin 1) ℝ) ^ k)) = 2 := by
  rw [tsum_eq_single 0]
  · rw [nm_pow, if_pos rfl]
  · intro k hk; rw [nm_pow, if_neg hk]

theorem cex : ¬ (∀ {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (normM : Matrix (Fin n) (Fin n) Real -> Real)
    (hsub : forall A B : Matrix (Fin n) (Fin n) Real, normM (A * B) <= normM A * normM B)
    (hnonneg : forall A : Matrix (Fin n) (Fin n) Real, 0 <= normM A)
    (hn : 1 <= n) (hQ1 : normM Q <= 1) (hgam : normM (Q ^ n) < 1),
    Summable (fun k : Nat => normM (Q ^ k)) /\
      (tsum fun k : Nat => normM (Q ^ k)) <= (n : Real) / (1 - normM (Q ^ n))) := by
  intro h
  have h1 : nm (0 : Matrix (Fin 1) (Fin 1) ℝ) ≤ 1 := by simp [nm]
  have h2 : nm ((0 : Matrix (Fin 1) (Fin 1) ℝ) ^ 1) < 1 := by simp [nm]
  have := (h (n := 1) 0 nm nm_sub nm_nonneg le_rfl h1 h2).2
  rw [tsum_nm] at this
  have h3 : nm ((0 : Matrix (Fin 1) (Fin 1) ℝ) ^ 1) = 0 := by simp [nm]
  rw [h3] at this
  norm_num at this

end CexChenWhitt2c2c

theorem solution : ¬ (∀ {n : Nat} (Q : Matrix (Fin n) (Fin n) Real)
    (normM : Matrix (Fin n) (Fin n) Real -> Real)
    (hsub : forall A B : Matrix (Fin n) (Fin n) Real, normM (A * B) <= normM A * normM B)
    (hnonneg : forall A : Matrix (Fin n) (Fin n) Real, 0 <= normM A)
    (hn : 1 <= n) (hQ1 : normM Q <= 1) (hgam : normM (Q ^ n) < 1),
    Summable (fun k : Nat => normM (Q ^ k)) /\
      (tsum fun k : Nat => normM (Q ^ k)) <= (n : Real) / (1 - normM (Q ^ n))) := by
  exact CexChenWhitt2c2c.cex
