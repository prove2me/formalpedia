-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.theorem_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T04:53:20.25297+00:00
-- url     : https://prove2.me/submissions/a1d11af4-bcc4-44f0-9e0e-a132146445b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CostlySeeding_EdgeQuery_theorem_7_spread
import Theorems.Thm_CostlySeeding_EdgeQuery_theorem_5
import Theorems.Thm_CostlySeeding_EdgeQuery_theorem_5_fixed_initial
import Theorems.Thm_CostlySeeding_EdgeQuery_worst_case_queries

open CostlySeeding.EdgeQuery

namespace T7Aux

/-! ### Seed weights -/

def seedEquiv (n : ℕ) : ProbeSeed n ≃
    (Fin (n + 1) → Equiv.Perm (Fin n)) ×
      (Fin n → Equiv.Perm (Fin n)) ×
      (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) where
  toFun s := (s.pick, s.order, s.coin, s.redo)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv := by intro s; cases s; rfl
  right_inv := by intro t; rcases t with ⟨a, b, c, d⟩; rfl

lemma sum_bitW (p : ℝ) : ∑ b : Bool, bitW p b = 1 := by
  simp [bitW]

lemma bitW_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : 0 ≤ bitW p b := by
  cases b <;> simp [bitW] <;> linarith

lemma sum_bits (n : ℕ) (p : ℝ) :
    ∑ c : Fin n → Fin n → Bool, ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w) = 1 := by
  rw [← Fintype.prod_sum (fun (v : Fin n) (r : Fin n → Bool) => ∏ w : Fin n, bitW p (r w))]
  apply Finset.prod_eq_one
  intro v _
  rw [← Fintype.prod_sum (fun (w : Fin n) (b : Bool) => bitW p b)]
  apply Finset.prod_eq_one
  intro w _
  exact sum_bitW p

lemma sum_perms (m n : ℕ) :
    ∑ _f : Fin m → Equiv.Perm (Fin n),
      ∏ _t : Fin m, (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) = 1 := by
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.prod_const, Finset.card_univ, Fintype.card_fun]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [div_pow, one_pow, mul_one_div, div_self (pow_ne_zero _ hc.ne')]

lemma sum_four {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ) :
    ∑ x : A × B × C × D, f x.1 * g x.2.1 * h x.2.2.1 * k x.2.2.2 =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ d, k d) := by
  simp only [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

lemma sum_seedW (n : ℕ) (p : ℝ) : ∑ s : ProbeSeed n, seedW p s = 1 := by
  rw [← (seedEquiv n).symm.sum_comp]
  have := sum_four
    (fun (a : Fin (n + 1) → Equiv.Perm (Fin n)) =>
      ∏ _t : Fin (n + 1), (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)))
    (fun (b : Fin n → Equiv.Perm (Fin n)) =>
      ∏ _t : Fin n, (1 / (Fintype.card (Equiv.Perm (Fin n)) : ℝ)))
    (fun (c : Fin n → Fin n → Bool) => ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w))
    (fun (c : Fin n → Fin n → Bool) => ∏ v : Fin n, ∏ w : Fin n, bitW p (c v w))
  simp only [sum_perms, sum_bits, mul_one] at this
  rw [← this]
  rfl

lemma seedW_nonneg (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ProbeSeed n) :
    0 ≤ seedW p s := by
  unfold seedW
  have h1 : ∀ v w : Fin n, 0 ≤ bitW p (s.coin v w) := fun _ _ => bitW_nonneg p hp0 hp1 _
  have h2 : ∀ v w : Fin n, 0 ≤ bitW p (s.redo v w) := fun _ _ => bitW_nonneg p hp0 hp1 _
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  · exact Finset.prod_nonneg fun _ _ => by positivity
  · exact Finset.prod_nonneg fun _ _ => by positivity
  · exact Finset.prod_nonneg fun v _ => Finset.prod_nonneg fun w _ => h1 v w
  · exact Finset.prod_nonneg fun v _ => Finset.prod_nonneg fun w _ => h2 v w

lemma sum_ssW (n T : ℕ) (p : ℝ) :
    ∑ ss : Fin T → ProbeSeed n, ∏ i : Fin T, seedW p (ss i) = 1 := by
  rw [← Fintype.sum_pow, sum_seedW, one_pow]

lemma ssW_nonneg (n T : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ss : Fin T → ProbeSeed n) :
    0 ≤ ∏ i : Fin T, seedW p (ss i) :=
  Finset.prod_nonneg fun i _ => seedW_nonneg n p hp0 hp1 (ss i)

/-! ### Averaging -/

lemma avg_upper {ι : Type} (s : Finset ι) (w X g : ι → ℝ) (Q M : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (h1 : ∑ i ∈ s, w i = 1)
    (hX : ∀ i ∈ s, X i ≤ Q + M * (1 - g i)) :
    ∑ i ∈ s, w i * X i ≤ Q + M - M * ∑ i ∈ s, w i * g i := by
  have : ∑ i ∈ s, w i * X i ≤ ∑ i ∈ s, w i * (Q + M * (1 - g i)) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hX i hi) (hw i hi)
  have e : ∑ i ∈ s, w i * (Q + M * (1 - g i)) = Q + M - M * ∑ i ∈ s, w i * g i := by
    have : ∀ i ∈ s, w i * (Q + M * (1 - g i)) = (Q + M) * w i - M * (w i * g i) := by
      intro i _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
    ring
  linarith

lemma uniform_sum {ι : Type} (s : Finset ι) (hs : s.Nonempty) :
    ∑ _i ∈ s, (1 / (s.card : ℝ)) = 1 := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hs).ne'
  field_simp

/-! ### The query bound -/

lemma powersetCard_univ_self (n : ℕ) :
    (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
  simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))

lemma inner_query {n T : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (V : Finset (Fin n)) (tau : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) * (queries G V tau ss : ℝ) ≤
      Q + 2 * T * n ^ 2 - 2 * T * n ^ 2 * ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
        (if (queries G V tau ss : ℝ) ≤ Q then 1 else 0) := by
  apply avg_upper _ _ _ _ Q _ (fun ss _ => ssW_nonneg n T p hp0 hp1 ss) (sum_ssW n T p)
  intro ss _
  have hw : (queries G V tau ss : ℝ) ≤ 2 * T * n ^ 2 := by
    exact_mod_cast worst_case_queries n T tau G V ss
  by_cases h : (queries G V tau ss : ℝ) ≤ Q
  · simp only [if_pos h, sub_self, mul_zero, add_zero]; exact h
  · simp only [if_neg h, sub_zero, mul_one]; linarith

lemma query_small (n k T : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℕ) (hm : m ≤ n) (tau : ℕ) (Q e : ℝ) (hQ : 0 ≤ Q)
    (h5 : 1 - 3 * e ≤ ∑ V ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        1 / (((Finset.univ : Finset (Fin n)).powersetCard m).card : ℝ) *
        ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
          (if (queries G V tau ss : ℝ) ≤ Q then 1 else 0)) :
    ∑ V ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        1 / (((Finset.univ : Finset (Fin n)).powersetCard m).card : ℝ) *
        ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) * (queries G V tau ss : ℝ) ≤
      Q + 2 * T * n ^ 2 * (3 * e) := by
  have hCne : ((Finset.univ : Finset (Fin n)).powersetCard m).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simpa using hm)
  have := avg_upper _ (fun _ => 1 / (((Finset.univ : Finset (Fin n)).powersetCard m).card : ℝ))
    (fun V => ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) * (queries G V tau ss : ℝ))
    (fun V => ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
          (if (queries G V tau ss : ℝ) ≤ Q then 1 else 0))
    Q (2 * T * n ^ 2) (fun _ _ => by positivity) (uniform_sum _ hCne) (by
      intro V _
      have := inner_query (T := T) G p hp0 hp1 V tau Q hQ
      linarith)
  refine le_trans this ?_
  have hM : (0 : ℝ) ≤ 2 * T * n ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h5 hM
  nlinarith

lemma query_large (n k T : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (tau : ℕ) (Q e : ℝ) (hQ : 0 ≤ Q)
    (h5 : 1 - 3 * e ≤ ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) *
          (if (queries G Finset.univ tau ss : ℝ) ≤ Q then 1 else 0)) :
    ∑ V ∈ (Finset.univ : Finset (Fin n)).powersetCard n,
        1 / (((Finset.univ : Finset (Fin n)).powersetCard n).card : ℝ) *
        ∑ ss : Fin T → ProbeSeed n, (∏ i, seedW p (ss i)) * (queries G V tau ss : ℝ) ≤
      Q + 2 * T * n ^ 2 * (3 * e) := by
  rw [powersetCard_univ_self, Finset.sum_singleton, Finset.card_singleton]
  have := inner_query (T := T) G p hp0 hp1 Finset.univ tau Q hQ
  have hM : (0 : ℝ) ≤ 2 * T * n ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h5 hM
  simp only [Nat.cast_one, div_one, one_mul]
  nlinarith

end T7Aux

theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (eps' : ℝ) (he0 : 0 < eps') (he1 : eps' ≤ 1)
    (hn : (30 / eps') ^ 2 ≤ (n : ℝ)) :
    (1 - Real.exp (-1)) * CostlySeeding.EdgeQuery.OPT G p k - eps' * n ≤
        CostlySeeding.EdgeQuery.algSpread G p k eps' ∧
    CostlySeeding.EdgeQuery.algQueries G p k eps' ≤
      CostlySeeding.EdgeQuery.QPar n k p (eps' / 7) (2 * Real.log n) +
        6 * CostlySeeding.EdgeQuery.TPar n k (eps' / 7) (2 * Real.log n) := by
  open T7Aux in
  -- numerical preliminaries
  have h900 : 900 ≤ (n : ℝ) * eps' ^ 2 := by
    have h := hn
    rw [div_pow, div_le_iff₀ (by positivity)] at h
    linarith
  have heps2 : eps' ^ 2 ≤ eps' := by nlinarith
  have hn900 : (900 : ℝ) ≤ n := by nlinarith
  have hn5 : 5 ≤ n := by
    have : (5 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by linarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogn' : Real.log n ≤ n := by
    have := Real.log_le_sub_one_of_pos hnR; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have heps : 0 < eps' / 7 := by positivity
  have heps7 : eps' / 7 ≤ 1 / 7 := by linarith
  have hexp : Real.exp (-(2 * Real.log n)) = 1 / (n : ℝ) ^ 2 := by
    have : 2 * Real.log n = Real.log ((n : ℝ) ^ 2) := by rw [Real.log_pow]; push_cast; ring
    rw [this, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hη : 2 * Real.exp (-(2 * Real.log n)) ≤ eps' / 7 := by
    rw [hexp, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    -- 14 ≤ eps' * n^2
    have : (900 : ℝ) * n ≤ eps' * n ^ 2 := by nlinarith
    nlinarith
  have he1' : Real.exp (-(2 * Real.log n)) ≤ 1 := by
    apply Real.exp_le_one_iff.2; linarith
  -- parameters
  have hTpos : 0 < TPar n k (eps' / 7) (2 * Real.log n) := by
    unfold TPar
    apply Nat.ceil_pos.2
    positivity
  have hρ0 : 0 < rhoPar n k (eps' / 7) (2 * Real.log n) := by
    unfold rhoPar
    positivity
  have hτ : 1 ≤ tauPar n k (eps' / 7) := by
    unfold tauPar
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    rw [Nat.ceil_eq_zero] at h0
    have hl : Real.log (eps' / 7) < 0 := Real.log_neg heps (by linarith)
    have : 0 < -((n : ℝ) * Real.log (eps' / 7)) / (eps' / 7 * k) := by
      apply div_pos _ (by positivity)
      nlinarith
    linarith
  have hQ0 : 0 ≤ QPar n k p (eps' / 7) (2 * Real.log n) := by
    unfold QPar CPar EPar
    have : (1 : ℝ) ≤ (tauPar n k (eps' / 7) : ℝ) := by exact_mod_cast hτ
    have : 0 ≤ p * (tauPar n k (eps' / 7) : ℝ) * ((tauPar n k (eps' / 7) : ℝ) - 1) / 2 := by
      apply div_nonneg _ (by norm_num)
      apply mul_nonneg (mul_nonneg hp0 (by linarith)) (by linarith)
    have := hρ0.le
    positivity
  have hTle : TPar n k (eps' / 7) (2 * Real.log n) ≤ n ^ 4 := by
    unfold TPar
    apply Nat.ceil_le.2
    rw [div_le_iff₀ (by positivity)]
    have hA : 2 * Real.log n + Real.log 2 ≤ 3 * n := by linarith
    have hK : (k : ℝ) + 1 ≤ 2 * n := by linarith
    have h1 : 3 * (2 * Real.log n + Real.log 2) * ((k : ℝ) + 1) * Real.log n ≤
        3 * (3 * n) * (2 * n) * n := by
      apply mul_le_mul _ hlogn' hlogn.le (by positivity)
      apply mul_le_mul _ hK (by positivity) (by positivity)
      linarith
    have h2 : 3 * (3 * (n : ℝ)) * (2 * n) * n ≤ ((n ^ 4 : ℕ) : ℝ) * (eps' / 7) ^ 2 := by
      push_cast
      have : (n : ℝ) ^ 4 * (eps' / 7) ^ 2 = (n : ℝ) ^ 3 * (n * eps' ^ 2) / 49 := by ring
      rw [this]
      have : (n : ℝ) ^ 3 * 900 ≤ (n : ℝ) ^ 3 * (n * eps' ^ 2) :=
        mul_le_mul_of_nonneg_left h900 (by positivity)
      nlinarith
    linarith
  have hsize : Real.sqrt (2 * Real.log n + Real.log (TPar n k (eps' / 7) (2 * Real.log n))) ≤ n := by
    have hT1 : (0 : ℝ) < TPar n k (eps' / 7) (2 * Real.log n) := by exact_mod_cast hTpos
    have hlT : Real.log (TPar n k (eps' / 7) (2 * Real.log n)) ≤ 4 * Real.log n := by
      have : ((TPar n k (eps' / 7) (2 * Real.log n) : ℕ) : ℝ) ≤ ((n ^ 4 : ℕ) : ℝ) := by
        exact_mod_cast hTle
      have := Real.log_le_log hT1 this
      rw [Nat.cast_pow, Real.log_pow] at this
      push_cast at this
      linarith
    calc _ ≤ Real.sqrt ((n : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith
      _ = n := Real.sqrt_sq hnR.le
  constructor
  · -- spread: the first conjunct is the child `theorem_7_spread`
    exact theorem_7_spread n k hk hkn G p hp0 hp1 eps' he0 he1 hn
  · -- queries
    have h6 : (6 : ℝ) * (TPar n k (eps' / 7) (2 * Real.log n) : ℝ) =
        2 * (TPar n k (eps' / 7) (2 * Real.log n) : ℝ) * n ^ 2 *
          (3 * Real.exp (-(2 * Real.log n))) := by
      rw [hexp]; field_simp; ring
    rw [h6]
    simp only [algQueries]
    by_cases hρ1 : rhoPar n k (eps' / 7) (2 * Real.log n) ≤ 1
    · have hm : initialSize n (rhoPar n k (eps' / 7) (2 * Real.log n)) =
          Nat.ceil ((n : ℝ) * rhoPar n k (eps' / 7) (2 * Real.log n)) := by
        unfold initialSize
        apply min_eq_left
        apply Nat.ceil_le.2
        have := mul_le_mul_of_nonneg_left hρ1 hnR.le
        linarith
      rw [hm]
      have h5 := theorem_5 n k hk hkn hn5 G p hp0 hp1 (eps' / 7) (2 * Real.log n) heps
        (by linarith) le_rfl hρ1 hsize
      simp only [probeEventProb] at h5
      apply query_small n k _ G p hp0 hp1 _ ?_ _ _ _ hQ0 h5
      apply Nat.ceil_le.2
      have := mul_le_mul_of_nonneg_left hρ1 hnR.le
      linarith
    · have hm : initialSize n (rhoPar n k (eps' / 7) (2 * Real.log n)) = n := by
        unfold initialSize
        apply min_eq_right
        have hρ1' : 1 < rhoPar n k (eps' / 7) (2 * Real.log n) := by push Not at hρ1; exact hρ1
        have : (n : ℝ) ≤ (Nat.ceil ((n : ℝ) * rhoPar n k (eps' / 7) (2 * Real.log n)) : ℝ) :=
          le_trans (by have := mul_le_mul_of_nonneg_left hρ1'.le hnR.le; linarith) (Nat.le_ceil _)
        exact_mod_cast this
      rw [hm]
      have h5 := theorem_5_fixed_initial n k hk hkn hn5 G p hp0 hp1 (eps' / 7) (2 * Real.log n)
        heps (by linarith) le_rfl hsize Finset.univ (by
          simp only [Finset.card_univ, Fintype.card_fin]
          have hρ1' : 1 < rhoPar n k (eps' / 7) (2 * Real.log n) := by push Not at hρ1; exact hρ1
          have := mul_le_mul_of_nonneg_left hρ1'.le hnR.le
          linarith)
      simp only [seedEventProb] at h5
      exact query_large n k _ G p hp0 hp1 _ _ _ hQ0 h5
