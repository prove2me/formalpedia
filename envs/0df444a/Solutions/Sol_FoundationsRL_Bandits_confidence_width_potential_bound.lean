-- Prove2me | solution 1 for FoundationsRL.Bandits.confidence_width_potential_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:38:40.726287+00:00
-- url     : https://prove2.me/submissions/85ed987b-1103-4ebd-89ff-8a16c9ca42cf

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount



namespace FoundationsRL.Bandits

lemma cw_succ {A : ℕ} (pi : ℕ → Fin A) (t : ℕ) (a : Fin A) :
    pullCount pi (t + 1) a = pullCount pi t a + (if pi t = a then 1 else 0) := by
  unfold pullCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma cw_regroup {A : ℕ} (pi : ℕ → Fin A) (f : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.range T, f (pullCount pi t (pi t)) =
      ∑ a : Fin A, ∑ k ∈ Finset.range (pullCount pi T a), f k := by
  induction T with
  | zero => simp [pullCount]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    have h : ∀ a : Fin A, ∑ k ∈ Finset.range (pullCount pi (T + 1) a), f k =
        ∑ k ∈ Finset.range (pullCount pi T a), f k
          + (if pi T = a then f (pullCount pi T a) else 0) := by
      intro a
      rw [cw_succ]
      split_ifs with h
      · rw [Finset.sum_range_succ]
      · simp
    rw [Finset.sum_congr rfl (fun a _ => h a), Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp

lemma cw_partial (N : ℕ) :
    ∑ k ∈ Finset.range N, (if k = 0 then (1:ℝ) else 1 / Real.sqrt k) ≤ 3 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      norm_num
    · rw [if_neg (by omega)]
      have hN : (1:ℝ) ≤ N := by exact_mod_cast hpos
      have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
      have hs1 : Real.sqrt (N:ℝ) ≤ Real.sqrt ((N:ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt ((N:ℝ) + 1) ≤ 2 * Real.sqrt N := by
        rw [show (2:ℝ) * Real.sqrt N = Real.sqrt (2 ^ 2 * N) by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hprod : (Real.sqrt ((N:ℝ) + 1) - Real.sqrt N) *
          (Real.sqrt ((N:ℝ) + 1) + Real.sqrt N) = 1 := by
        have e1 := Real.sq_sqrt (show (0:ℝ) ≤ N + 1 by positivity)
        have e2 := Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)
        nlinarith
      have hd : 0 ≤ Real.sqrt ((N:ℝ) + 1) - Real.sqrt N := by linarith
      have hm := mul_le_mul_of_nonneg_left
        (show Real.sqrt ((N:ℝ) + 1) + Real.sqrt N ≤ 3 * Real.sqrt N by linarith) hd
      have key : 1 / Real.sqrt N ≤ 3 * (Real.sqrt ((N:ℝ) + 1) - Real.sqrt N) := by
        rw [div_le_iff₀ hsN]
        calc (1:ℝ) = (Real.sqrt ((N:ℝ) + 1) - Real.sqrt N) *
              (Real.sqrt ((N:ℝ) + 1) + Real.sqrt N) := hprod.symm
          _ ≤ (Real.sqrt ((N:ℝ) + 1) - Real.sqrt N) * (3 * Real.sqrt N) := hm
          _ = 3 * (Real.sqrt ((N:ℝ) + 1) - Real.sqrt N) * Real.sqrt N := by ring
      push_cast
      linarith

theorem cw_main : ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (T : ℕ) (pi : ℕ → Fin A),
        ∑ t ∈ Finset.range T,
            (if pullCount pi t (pi t) = 0 then (1 : ℝ)
              else 1 / Real.sqrt (pullCount pi t (pi t)))
          ≤ C * Real.sqrt ((A : ℝ) * T) := by
  refine ⟨3, by norm_num, fun A _ T pi => ?_⟩
  rw [cw_regroup pi (fun k : ℕ => if k = 0 then (1:ℝ) else 1 / Real.sqrt k) T]
  have htot : ∑ a : Fin A, (pullCount pi T a : ℝ) = T := by
    have := Finset.card_eq_sum_card_fiberwise (f := pi) (s := Finset.range T)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_range] at this
    unfold pullCount
    exact_mod_cast this.symm
  calc ∑ a : Fin A, ∑ k ∈ Finset.range (pullCount pi T a),
        (fun k : ℕ => if k = 0 then (1:ℝ) else 1 / Real.sqrt k) k
      ≤ ∑ a : Fin A, 3 * Real.sqrt (pullCount pi T a) :=
        Finset.sum_le_sum fun a _ => cw_partial _
    _ = 3 * ∑ a : Fin A, Real.sqrt (pullCount pi T a) := by rw [Finset.mul_sum]
    _ ≤ 3 * Real.sqrt ((A : ℝ) * T) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin A => (1:ℝ))
          (fun a => Real.sqrt (pullCount pi T a))
        have hsq : ∑ a : Fin A, Real.sqrt (pullCount pi T a) ^ 2 = T := by
          rw [← htot]
          exact Finset.sum_congr rfl fun a _ => Real.sq_sqrt (Nat.cast_nonneg _)
        simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, hsq] at hcs
        exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)

end FoundationsRL.Bandits

open FoundationsRL.Bandits

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (T : ℕ) (pi : ℕ → Fin A),
        ∑ t ∈ Finset.range T,
            (if pullCount pi t (pi t) = 0 then (1 : ℝ)
              else 1 / Real.sqrt (pullCount pi t (pi t)))
          ≤ C * Real.sqrt ((A : ℝ) * T) := by
  exact cw_main
