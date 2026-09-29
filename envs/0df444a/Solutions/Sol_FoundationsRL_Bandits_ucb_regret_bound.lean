-- Prove2me | solution 1 for FoundationsRL.Bandits.ucb_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T06:19:28.246469+00:00
-- url     : https://prove2.me/submissions/f55dfba9-db2a-44d3-8ef1-637ba19f281a

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_regret
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_FoundationsRL_Bandits_confidenceRadius



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


lemma cw_bound {A : ℕ} (T : ℕ) (pi : ℕ → Fin A) :
    ∑ t ∈ Finset.range T,
        (if pullCount pi t (pi t) = 0 then (1 : ℝ) else 1 / Real.sqrt (pullCount pi t (pi t)))
      ≤ 3 * Real.sqrt ((A : ℝ) * T) := by
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

theorem ucb_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (pi : ℕ → Fin A) (fhat : ℕ → Fin A → ℝ),
          (∀ t : ℕ, (∃ a : Fin A, pullCount pi t a = 0) → pullCount pi t (pi t) = 0) →
          (∀ t : ℕ, (∀ a : Fin A, pullCount pi t a ≠ 0) → ∀ a : Fin A,
              fhat t a + confidenceRadius T A δ (pullCount pi t a) ≤
                fhat t (pi t) + confidenceRadius T A δ (pullCount pi t (pi t))) →
          (∀ t ∈ Finset.range T, ∀ a : Fin A, pullCount pi t a ≠ 0 →
              |fhat t a - fStar a| ≤ confidenceRadius T A δ (pullCount pi t a)) →
          regret fStar piStar T (fun t a => if a = pi t then (1 : ℝ) else 0) ≤
            C * Real.sqrt ((A : ℝ) * T * Real.log ((A : ℝ) * T / δ)) := by
  refine ⟨18, by norm_num, ?_⟩
  intro A hA fStar hf01 piStar hstar T hT δ hδ hδ1 pi fhat huns hucb hgood
  -- the regret of a Dirac play
  have hreg : regret fStar piStar T (fun t a => if a = pi t then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range T, (fStar piStar - fStar (pi t)) := by
    unfold regret
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [ite_mul]
  rw [hreg]
  have hRHS0 : 0 ≤ (18:ℝ) * Real.sqrt ((A : ℝ) * T * Real.log ((A : ℝ) * T / δ)) := by positivity
  rcases Nat.lt_or_ge A 2 with hA1 | hA2
  · -- a single action: no regret
    have hsub : ∀ a b : Fin A, a = b := by
      intro a b; apply Fin.ext; omega
    have h0 : ∑ t ∈ Finset.range T, (fStar piStar - fStar (pi t)) = 0 :=
      Finset.sum_eq_zero fun t _ => by rw [hsub piStar (pi t), sub_self]
    rw [h0]; exact hRHS0
  · have hAR : (2:ℝ) ≤ A := by exact_mod_cast hA2
    have hTR : (1:ℝ) ≤ T := by exact_mod_cast hT
    set L := Real.log ((A : ℝ) * T / δ) with hL
    set L' := Real.log (2 * (T : ℝ) ^ 2 * (A : ℝ) / δ) with hL'
    have hq2 : (2:ℝ) ≤ (A : ℝ) * T / δ := by
      rw [le_div_iff₀ hδ]; nlinarith
    have hLpos : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hq2
    have hlog2 : (1/4 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hL0 : 0 < L := lt_of_lt_of_le (by linarith) hLpos
    have hL'le : L' ≤ 2 * L := by
      have e : 2 * (T : ℝ) ^ 2 * (A : ℝ) / δ = (2 * T) * ((A : ℝ) * T / δ) := by ring
      rw [hL', e, Real.log_mul (by positivity) (by positivity)]
      have : Real.log (2 * (T:ℝ)) ≤ L := Real.log_le_log (by positivity) (by
        rw [le_div_iff₀ hδ]; nlinarith)
      linarith
    have hL'0 : 0 ≤ L' := by
      rw [hL']; apply Real.log_nonneg; rw [le_div_iff₀ hδ]; nlinarith
    set K : ℝ := 1 + 2 * Real.sqrt (2 * L') with hK
    have hK1 : 1 ≤ K := by rw [hK]; linarith [Real.sqrt_nonneg (2 * L')]
    -- per-round bound
    have hround : ∀ t ∈ Finset.range T, fStar piStar - fStar (pi t) ≤
        K * (if pullCount pi t (pi t) = 0 then (1 : ℝ) else 1 / Real.sqrt (pullCount pi t (pi t))) := by
      intro t ht
      by_cases hz : pullCount pi t (pi t) = 0
      · rw [if_pos hz, mul_one]
        have := (hf01 piStar).2; have := (hf01 (pi t)).1
        linarith
      · rw [if_neg hz]
        have hall : ∀ a : Fin A, pullCount pi t a ≠ 0 := by
          intro a ha
          exact hz (huns t ⟨a, ha⟩)
        have hn : (0:ℝ) < pullCount pi t (pi t) := by exact_mod_cast Nat.pos_of_ne_zero hz
        have h1 := abs_le.mp (hgood t ht piStar (hall piStar))
        have h2 := abs_le.mp (hgood t ht (pi t) hz)
        have h3 := hucb t hall piStar
        have hconf : confidenceRadius T A δ (pullCount pi t (pi t)) =
            Real.sqrt (2 * L') * (1 / Real.sqrt (pullCount pi t (pi t))) := by
          unfold confidenceRadius
          rw [Real.sqrt_div' _ hn.le, mul_one_div]
        have hg0 : 0 ≤ 1 / Real.sqrt (pullCount pi t (pi t) : ℝ) := by positivity
        have hmono : 2 * Real.sqrt (2 * L') * (1 / Real.sqrt (pullCount pi t (pi t))) ≤
            K * (1 / Real.sqrt (pullCount pi t (pi t))) :=
          mul_le_mul_of_nonneg_right (by rw [hK]; linarith) hg0
        linarith
    have hsum := Finset.sum_le_sum hround
    rw [← Finset.mul_sum] at hsum
    have hpot := cw_bound (A := A) T pi
    have hK0 : 0 ≤ K := by linarith
    have hKL : K ≤ 6 * Real.sqrt L := by
      have hs1 : Real.sqrt (2 * L') ≤ 2 * Real.sqrt L := by
        rw [show (2:ℝ) * Real.sqrt L = Real.sqrt (2 ^ 2 * L) by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hs2 : 1 ≤ 2 * Real.sqrt L := by
        have : (1/2 : ℝ) ≤ Real.sqrt L := by
          rw [show (1/2 : ℝ) = Real.sqrt ((1/2) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by nlinarith)
        linarith
      rw [hK]; linarith
    have hfin : K * (3 * Real.sqrt ((A : ℝ) * T)) ≤
        18 * Real.sqrt ((A : ℝ) * T * L) := by
      rw [Real.sqrt_mul (by positivity) L]
      have hs := Real.sqrt_nonneg ((A : ℝ) * T)
      nlinarith [mul_le_mul_of_nonneg_right hKL (by positivity : (0:ℝ) ≤ 3 * Real.sqrt ((A : ℝ) * T))]
    calc ∑ t ∈ Finset.range T, (fStar piStar - fStar (pi t))
        ≤ K * ∑ t ∈ Finset.range T, (if pullCount pi t (pi t) = 0 then (1 : ℝ)
            else 1 / Real.sqrt (pullCount pi t (pi t))) := hsum
      _ ≤ K * (3 * Real.sqrt ((A : ℝ) * T)) := mul_le_mul_of_nonneg_left hpot hK0
      _ ≤ 18 * Real.sqrt ((A : ℝ) * T * L) := hfin

end FoundationsRL.Bandits

open FoundationsRL.Bandits

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (pi : ℕ → Fin A) (fhat : ℕ → Fin A → ℝ),
          -- if some action is still unsampled, UCB plays an unsampled action
          -- (its upper confidence bound is `+∞` in the book).
          (∀ t : ℕ, (∃ a : Fin A, pullCount pi t a = 0) → pullCount pi t (pi t) = 0) →
          -- once every action has been sampled, `pi t` maximizes the upper confidence bound.
          (∀ t : ℕ, (∀ a : Fin A, pullCount pi t a ≠ 0) → ∀ a : Fin A,
              fhat t a + confidenceRadius T A δ (pullCount pi t a) ≤
                fhat t (pi t) + confidenceRadius T A δ (pullCount pi t (pi t))) →
          -- Eq. (2.18): the good event, holding with probability at least `1 - δ`,
          -- restricted to sampled actions (vacuous otherwise in the book).
          (∀ t ∈ Finset.range T, ∀ a : Fin A, pullCount pi t a ≠ 0 →
              |fhat t a - fStar a| ≤ confidenceRadius T A δ (pullCount pi t a)) →
          regret fStar piStar T (fun t a => if a = pi t then (1 : ℝ) else 0) ≤
            C * Real.sqrt ((A : ℝ) * T * Real.log ((A : ℝ) * T / δ)) := by
  exact ucb_main
