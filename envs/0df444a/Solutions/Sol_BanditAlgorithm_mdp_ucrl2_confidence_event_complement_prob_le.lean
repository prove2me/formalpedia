-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_confidence_event_complement_prob_le
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-03T02:51:18.569438+00:00
-- url     : https://prove2.me/submissions/de5336d3-d770-4a76-be27-f036324b2e37

import Theorems.Thm_BanditAlgorithm_mdp_empirical_row_deviation_at_sample_size_prob_le
import Theorems.Thm_BanditAlgorithm_mdp_confidence_union_bound_arithmetic

open MeasureTheory ProbabilityTheory ENNReal BanditAlgorithm

/-!
The statistical half of the analysis of UCRL2: the confidence event fails with
probability at most `δ / 2`.

The failure of the confidence event at some time `k ≤ n` for some pair `(s, a)`
is a statement about the empirical row built out of the transitions observed so
far, and that row depends on `k` only through the number `m` of observations it
is built from.  So the failure is covered by the events "the empirical row of
`(s, a)` at sample size `m` deviates by more than the radius at sample size
`m`", one for each pair and each `m ≤ n`; the first child bounds each of these by
`2 ^ S exp (-7 S log (2 S A n / δ))`, and the arithmetic of the second child
collects the `S * A * n` of them into `δ / 2`.  The sample size `m = 0` needs no
probabilistic input: an `L¹` distance between probability vectors never exceeds
`2`, which is already below the radius at sample size `0`.
-/

theorem solution
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (M : FiniteMDP S A) (π : MDPPolicy S A) (μ0 : MDPStateDistribution S) :
    mdpMeasure M μ0 π n (mdpConfidenceGoodEvent M n δ)ᶜ ≤ ENNReal.ofReal (δ / 2) := by
  classical
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hS0 : 0 < S := by omega
  have hSR : (2 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hAR : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `Y = 2 S A n / δ ≥ 4`, so its logarithm is at least `3/4`.
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hprod : (4 : ℝ) ≤ 2 * S * A * n := by
    have e1 : (4 : ℝ) * 1 ≤ 2 * (S : ℝ) * A :=
      mul_le_mul (by linarith) hAR (by norm_num) (by linarith)
    have e2 : (4 : ℝ) * 1 ≤ 2 * (S : ℝ) * A * n :=
      mul_le_mul (by linarith) hnR (by norm_num) (by linarith)
    linarith
  have hY4 : (4 : ℝ) ≤ 2 * S * A * n / δ := by
    rw [le_div_iff₀ hδ0]; nlinarith
  have hY0 : (0 : ℝ) < 2 * S * A * n / δ := by linarith
  have hL34 : (3 / 4 : ℝ) ≤ Real.log (2 * S * A * n / δ) := by
    have h1 : Real.log ((2 * S * A * n / δ)⁻¹) ≤ (2 * S * A * n / δ)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h1
    have h2 : (2 * S * A * n / δ)⁻¹ ≤ (4 : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hY4
    linarith
  have hL0 : (0 : ℝ) ≤ Real.log (2 * S * A * n / δ) := by linarith
  have h14 : (4 : ℝ) ≤ 14 * S * Real.log (2 * S * A * n / δ) := by nlinarith
  -- the bad event at sample size `j + 1`
  set Bad : Fin S → Fin A → ℕ → Set (MDPTrajectory S A n) := fun s a j ↦
    {h | ∃ k ≤ n, mdpObservedCount h k s a = j + 1 ∧
      mdpConfidenceRadius S A n δ (j + 1)
        ≤ ∑ s', |mdpEmpiricalRow h k s a s' - (M.P s a s' : ℝ)|} with hBaddef
  -- the confidence radius after `j+1` observations, squared
  have hradsq : ∀ j : ℕ,
      mdpConfidenceRadius S A n δ (j + 1) ^ 2
        = 14 * S * Real.log (2 * S * A * n / δ) / ((j + 1 : ℕ) : ℝ) := by
    intro j
    simp only [mdpConfidenceRadius]
    rw [show max 1 (j + 1) = j + 1 from max_eq_right (by omega)]
    refine Real.sq_sqrt (div_nonneg (mul_nonneg (by positivity) hL0) (by positivity))
  have hradnn : ∀ j : ℕ, 0 ≤ mdpConfidenceRadius S A n δ (j + 1) := fun j ↦
    Real.sqrt_nonneg _
  -- the deviation bound at each fixed sample size
  have hW : ∀ (s : Fin S) (a : Fin A) (j : ℕ),
      (mdpMeasure M μ0 π n).real (Bad s a j)
        ≤ 2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ))) := by
    intro s a j
    have hw := BanditAlgorithm.mdp_empirical_row_deviation_at_sample_size_prob_le
      S A n hS0 hA M μ0 π s a (j + 1) (Nat.succ_pos j) (hradnn j)
    have hexp : -(((j + 1 : ℕ) : ℝ)) * mdpConfidenceRadius S A n δ (j + 1) ^ 2 / 2
        = -(7 * S * Real.log (2 * S * A * n / δ)) := by
      rw [hradsq j]
      have hne : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hexp] at hw
    exact hw
  -- the number of transitions observed out of a pair never exceeds the horizon
  have hcount_le : ∀ (h : MDPTrajectory S A n) (k : ℕ) (s : Fin S) (a : Fin A),
      mdpObservedCount h k s a ≤ n := by
    intro h k s a
    simp only [mdpObservedCount, mdpTransitionCount, Finset.card_filter]
    rw [Finset.sum_comm]
    have hstep : ∀ i : Fin n,
        (∑ s' : Fin S, if i.val + 1 < k ∧ h i = (s, a) ∧ mdpSuccessor h i = some s'
          then 1 else 0) ≤ 1 := by
      intro i
      rcases hsucc : mdpSuccessor h i with _ | x
      · simp
      · refine le_trans (Finset.sum_le_sum
          (g := fun s' : Fin S ↦ if s' = x then 1 else 0) fun s' _ ↦ ?_) (by simp)
        by_cases hx : s' = x
        · rw [if_pos hx]; split <;> simp
        · simp [hx, Ne.symm hx]
    calc (∑ i : Fin n, ∑ s' : Fin S,
            if i.val + 1 < k ∧ h i = (s, a) ∧ mdpSuccessor h i = some s' then 1 else 0)
        ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ ↦ hstep i
      _ = n := by simp
  -- the failure of the confidence event is covered by the bad events
  have hsub : (mdpConfidenceGoodEvent M n δ)ᶜ ⊆
      ⋃ p : Fin S × Fin A × Fin n, Bad p.1 p.2.1 p.2.2 := by
    intro h hh
    simp only [Set.mem_compl_iff, mdpConfidenceGoodEvent, Set.mem_setOf_eq] at hh
    push_neg at hh
    obtain ⟨k, hk, s, a, hfail⟩ := hh
    have h1 : ∀ s', (0 : ℝ) ≤ (M.P s a s' : ℝ) := fun s' ↦ (M.P s a s').coe_nonneg
    have h2 : ∑ s', (M.P s a s' : ℝ) = 1 := by
      rw [← NNReal.coe_sum, M.P_sum_one]; simp
    have h3 : ¬ (∑ s', |(M.P s a s' : ℝ) - mdpEmpiricalRow h k s a s'|
        ≤ mdpConfidenceRadius S A n δ (mdpObservedCount h k s a)) := fun hc ↦
      hfail ⟨h1, h2, hc⟩
    push_neg at h3
    rcases Nat.eq_zero_or_pos (mdpObservedCount h k s a) with hm0 | hmpos
    · -- with no observation the radius already exceeds any `L¹` distance
      exfalso
      have hemp : ∀ s', mdpEmpiricalRow h k s a s' = if s' = s then 1 else 0 := by
        intro s'; simp [mdpEmpiricalRow, hm0]
      have hle2 : ∑ s', |(M.P s a s' : ℝ) - mdpEmpiricalRow h k s a s'| ≤ 2 := by
        calc ∑ s', |(M.P s a s' : ℝ) - mdpEmpiricalRow h k s a s'|
            ≤ ∑ s', ((M.P s a s' : ℝ) + if s' = s then 1 else 0) := by
              refine Finset.sum_le_sum fun s' _ ↦ ?_
              rw [hemp s']
              refine (abs_sub _ _).trans ?_
              rw [abs_of_nonneg (h1 s'), abs_of_nonneg (by positivity)]
          _ = 1 + 1 := by rw [Finset.sum_add_distrib, h2]; simp
          _ = 2 := by norm_num
      have hrad2 : (2 : ℝ) ≤ mdpConfidenceRadius S A n δ (mdpObservedCount h k s a) := by
        rw [hm0]
        simp only [mdpConfidenceRadius]
        rw [show max 1 0 = 1 from rfl, Nat.cast_one, div_one]
        calc (2 : ℝ) = Real.sqrt 4 := hsq4.symm
          _ ≤ _ := Real.sqrt_le_sqrt h14
      linarith
    · -- with `j + 1 ≥ 1` observations the sample size determines the empirical row
      obtain ⟨j, hj⟩ : ∃ j, mdpObservedCount h k s a = j + 1 :=
        ⟨mdpObservedCount h k s a - 1, by omega⟩
      have hjn : j < n := by
        have := hcount_le h k s a; omega
      refine Set.mem_iUnion.2 ⟨(s, a, ⟨j, hjn⟩), ?_⟩
      simp only [hBaddef, Set.mem_setOf_eq]
      refine ⟨k, hk, hj, ?_⟩
      rw [hj] at h3
      refine le_of_lt (lt_of_lt_of_le h3 ?_)
      refine le_of_eq (Finset.sum_congr rfl fun s' _ ↦ ?_)
      rw [abs_sub_comm]
  -- collecting the pieces
  have hBadle : ∀ (s : Fin S) (a : Fin A) (j : ℕ),
      mdpMeasure M μ0 π n (Bad s a j)
        ≤ ENNReal.ofReal (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ)))) := by
    intro s a j
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)]
    simpa [measureReal_def] using hW s a j
  calc mdpMeasure M μ0 π n (mdpConfidenceGoodEvent M n δ)ᶜ
      ≤ mdpMeasure M μ0 π n (⋃ p : Fin S × Fin A × Fin n, Bad p.1 p.2.1 p.2.2) :=
        measure_mono hsub
    _ ≤ ∑' p : Fin S × Fin A × Fin n, mdpMeasure M μ0 π n (Bad p.1 p.2.1 p.2.2) :=
        measure_iUnion_le _
    _ = ∑ p : Fin S × Fin A × Fin n, mdpMeasure M μ0 π n (Bad p.1 p.2.1 p.2.2) :=
        tsum_fintype _
    _ ≤ ∑ _p : Fin S × Fin A × Fin n,
          ENNReal.ofReal (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ)))) :=
        Finset.sum_le_sum fun p _ ↦ hBadle _ _ _
    _ = ((S * A * n : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ)))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 2
        simp only [Fintype.card_prod, Fintype.card_fin]
        ring
    _ ≤ ENNReal.ofReal (δ / 2) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have harith :=
          BanditAlgorithm.mdp_confidence_union_bound_arithmetic S A n hS hA hn δ
            ⟨hδ0, hδ1⟩
        calc ((S * A * n : ℕ) : ℝ) *
              (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ))))
            = (S : ℝ) * A * n *
              (2 ^ S * Real.exp (-(7 * S * Real.log (2 * S * A * n / δ)))) := by
              push_cast; ring
          _ ≤ δ / 2 := harith
