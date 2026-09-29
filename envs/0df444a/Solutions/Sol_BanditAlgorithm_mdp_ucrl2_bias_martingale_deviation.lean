-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_bias_martingale_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-03T03:03:04.791783+00:00
-- url     : https://prove2.me/submissions/f8873fd6-5568-4f8a-9219-d8504f8c5821

import Theorems.Thm_BanditAlgorithm_mdp_trajectory_azuma_of_centered_bounded_increments
import Theorems.Thm_BanditAlgorithm_mdp_optimistic_bias_span_le_diameter
import Theorems.Thm_BanditAlgorithm_mdp_compact_confidence_optimistic_bellman_solution
import Theorems.Thm_BanditAlgorithm_prob_vector_l1_ball_nonempty_isCompact

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm

namespace BiasMg

variable {S A : ℕ}

/-! ### The data of a round depends only on the rounds already played -/

section Prefix

variable {n : ℕ}

lemma successor_congr {t : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) (i : Fin n) (hi : i.val + 1 ≤ t) :
    mdpSuccessor h i = mdpSuccessor h' i := by
  simp only [mdpSuccessor]
  by_cases hlt : i.val + 1 < n
  · rw [dif_pos hlt, dif_pos hlt, hag ⟨i.val + 1, hlt⟩ hi]
  · rw [dif_neg hlt, dif_neg hlt]

lemma visitCount_congr {t k : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) (hk : k ≤ t + 1) (s : Fin S) (a : Fin A) :
    mdpVisitCount h k s a = mdpVisitCount h' k s a := by
  classical
  simp only [mdpVisitCount]
  congr 1
  refine Finset.filter_congr fun i _ ↦ ?_
  by_cases hik : i.val < k
  · rw [hag i (by omega)]
  · simp [hik]

lemma transitionCount_congr {t k : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) (hk : k ≤ t + 1)
    (s : Fin S) (a : Fin A) (s' : Fin S) :
    mdpTransitionCount h k s a s' = mdpTransitionCount h' k s a s' := by
  classical
  simp only [mdpTransitionCount]
  congr 1
  refine Finset.filter_congr fun i _ ↦ ?_
  by_cases hik : i.val + 1 < k
  · rw [hag i (by omega), successor_congr hag i (by omega)]
  · simp [hik]

lemma observedCount_congr {t k : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) (hk : k ≤ t + 1) (s : Fin S) (a : Fin A) :
    mdpObservedCount h k s a = mdpObservedCount h' k s a := by
  simp only [mdpObservedCount]
  exact Finset.sum_congr rfl fun s' _ ↦ transitionCount_congr hag hk s a s'

lemma empiricalRow_congr {t k : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) (hk : k ≤ t + 1) (s : Fin S) (a : Fin A) :
    mdpEmpiricalRow h k s a = mdpEmpiricalRow h' k s a := by
  simp only [mdpEmpiricalRow, observedCount_congr hag hk s a]
  by_cases h0 : mdpObservedCount h' k s a = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    exact funext fun s' ↦ by rw [transitionCount_congr hag hk s a s']

lemma confidenceSet_congr {t k : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) (hk : k ≤ t + 1) (m : ℕ) (δ : ℝ)
    (s : Fin S) (a : Fin A) :
    mdpConfidenceSet h k m δ s a = mdpConfidenceSet h' k m δ s a := by
  simp only [mdpConfidenceSet, empiricalRow_congr hag hk s a, observedCount_congr hag hk s a]

lemma phaseStart_le {h : MDPTrajectory S A n} : ∀ u, mdpPhaseStart h u ≤ u := by
  intro u
  induction u with
  | zero => exact le_rfl
  | succ u ih =>
      simp only [mdpPhaseStart]
      split
      · exact le_rfl
      · omega

lemma phaseStart_congr {t : ℕ} {h h' : MDPTrajectory S A n}
    (hag : ∀ i : Fin n, i.val ≤ t → h i = h' i) :
    ∀ u ≤ t, mdpPhaseStart h u = mdpPhaseStart h' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
      intro hu
      have hτ : mdpPhaseStart h u = mdpPhaseStart h' u := ih (by omega)
      simp only [mdpPhaseStart, hτ]
      have hle : mdpPhaseStart h' u ≤ u := phaseStart_le u
      have e1 : ∀ (s : Fin S) (a : Fin A),
          mdpVisitCount h (u + 1) s a = mdpVisitCount h' (u + 1) s a :=
        fun s a ↦ visitCount_congr hag (by omega) s a
      have e2 : ∀ (s : Fin S) (a : Fin A),
          mdpVisitCount h (mdpPhaseStart h' u) s a
            = mdpVisitCount h' (mdpPhaseStart h' u) s a :=
        fun s a ↦ visitCount_congr hag (by omega) s a
      simp only [e1, e2]

end Prefix

/-! ### The empirical row is a probability vector -/

lemma empiricalRow_nonneg {n k : ℕ} (h : MDPTrajectory S A n) (s : Fin S) (a : Fin A)
    (s' : Fin S) : 0 ≤ mdpEmpiricalRow h k s a s' := by
  classical
  simp only [mdpEmpiricalRow]
  by_cases h0 : mdpObservedCount h k s a = 0
  · rw [if_pos h0]
    by_cases hs : s' = s <;> simp [hs]
  · rw [if_neg h0]
    positivity

lemma empiricalRow_sum {n k : ℕ} (h : MDPTrajectory S A n) (s : Fin S) (a : Fin A) :
    ∑ s', mdpEmpiricalRow h k s a s' = 1 := by
  classical
  simp only [mdpEmpiricalRow]
  by_cases h0 : mdpObservedCount h k s a = 0
  · rw [if_pos h0]
    simp
  · rw [if_neg h0]
    rw [← Finset.sum_div]
    have : ∑ s' : Fin S, ((mdpTransitionCount h k s a s' : ℕ) : ℝ)
        = ((mdpObservedCount h k s a : ℕ) : ℝ) := by
      rw [mdpObservedCount]; push_cast; ring
    rw [this, div_self (by exact_mod_cast h0)]

end BiasMg

open BiasMg

/-!
The martingale term of the regret of UCRL2 is at most `D √(2 n log (2 / δ))`
outside an event of probability `δ / 2`.

The summand at time `t` is the difference between the average of the bias of the
current phase under the true transition row out of the round played at time `t`
and the realised value of that bias at the state of round `t + 1`.  The bias is
a function of the confidence sets of the phase, which are built from the
transitions recorded strictly before the start of the phase, so the summand
depends on the trajectory only through the rounds up to `t` and through the
state of round `t + 1`; averaging it over that state against the true row gives
`0`.  Its size is at most the span of the bias, and the second child bounds that
span by the diameter of the true MDP as long as the true rows lie in the
confidence sets -- which is guaranteed by the confidence event, but only there,
so the summand is switched off as soon as the confidence event has failed at
some time up to `t + 1`; that switch is again a function of the rounds up to
`t`, and it changes nothing on the confidence event.  The first child is the
Azuma--Hoeffding inequality for such sums along an MDP trajectory, and it gives
the deviation `ε = D √(2 n log (2 / δ))` a probability at most
`exp (-n log (2 / δ) / (n - 1)) ≤ δ / 2`.
-/

theorem solution
    (S A n : ℕ) [NeZero A] (hS : 2 ≤ S) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1)
    (M : FiniteMDP S A) (hMr : M.r = r) (hD : 1 ≤ mdpDiameter M)
    (μ0 : MDPStateDistribution S) :
    ∃ E : Set (MDPTrajectory S A n),
      mdpMeasure M μ0 (ucrl2Policy n δ r) n Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
      ∀ h ∈ mdpConfidenceGoodEvent M n δ ∩ E,
      ∀ (st : ℕ → Fin S) (act : ℕ → Fin A), (∀ t : Fin n, h t = (st t, act t)) →
        ∑ t ∈ Finset.range (n - 1),
            ((∑ s', (M.P (st t) (act t) s' : ℝ)
                * mdpOptimisticBias r
                    (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a) s')
              - mdpOptimisticBias r
                  (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a)
                  (st (t + 1)))
          ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ)) := by
  classical
  obtain ⟨hδ0, hδ1⟩ := hδ
  have hS0 : 0 < S := by omega
  set D : ℝ := mdpDiameter M with hDdef
  set L : ℝ := Real.log (2 / δ) with hLdef
  set ε : ℝ := D * Real.sqrt (2 * n * L) with hεdef
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : 0 < L := by
    rw [hLdef]
    have : (1 : ℝ) < 2 / δ := by rw [lt_div_iff₀ hδ0]; linarith
    exact Real.log_pos this
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrad : 0 ≤ 2 * (n : ℝ) * L := by positivity
  have hε0 : 0 ≤ ε := by positivity
  have hexpL : Real.exp (-L) = δ / 2 := by
    rw [hLdef, Real.exp_neg, Real.exp_log (by positivity)]
    rw [inv_div]
  -- the bias of the phase current at time `t`
  set C : MDPTrajectory S A n → ℕ → Fin S → Fin A → Set (Fin S → ℝ) := fun h t x a ↦
    mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a with hCdef
  set v : MDPTrajectory S A n → ℕ → Fin S → ℝ := fun h t ↦
    mdpOptimisticBias r (C h t) with hvdef
  -- the confidence event has not failed at any time up to `t + 1`
  set Gd : MDPTrajectory S A n → ℕ → Prop := fun h t ↦
    ∀ k ≤ t + 1, ∀ (x : Fin S) (a : Fin A),
      (fun s' ↦ ((M.P x a s' : ℝ))) ∈ mdpConfidenceSet h k n δ x a with hGddef
  -- the stopped increment
  set G : MDPTrajectory S A n → ℕ → Fin S → ℝ := fun h t s' ↦
    if ht : t < n then
      (if Gd h t then
        (∑ s'', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) * v h t s'') - v h t s'
      else 0)
    else 0 with hGdef
  -- an optimistic plan exists for the confidence balls of any history
  have hplan : ∀ (h : MDPTrajectory S A n) (t : ℕ), Gd h t →
      ∃ (ρ : ℝ) (w : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
        IsOptimisticPlan r (C h t) ρ w f q := by
    intro h t hgd
    have hDne : mdpDiameterENN M ≠ ⊤ := by
      intro htop
      rw [hDdef, mdpDiameter, htop, ENNReal.toReal_top] at hD0
      linarith
    have hball : ∀ (x : Fin S) (a : Fin A),
        (C h t x a).Nonempty ∧ IsCompact (C h t x a) := by
      intro x a
      have := BanditAlgorithm.prob_vector_l1_ball_nonempty_isCompact
        (mdpEmpiricalRow h (mdpPhaseStart h t + 1) x a)
        (empiricalRow_nonneg h x a) (empiricalRow_sum h x a)
        (mdpConfidenceRadius S A n δ (mdpObservedCount h (mdpPhaseStart h t + 1) x a))
        (Real.sqrt_nonneg _)
      obtain ⟨⟨p, hp⟩, hcomp⟩ := this
      refine ⟨⟨p, hp⟩, hcomp⟩
    obtain ⟨ρ, w, f, q, h1, h2, -, h4, h5, h6, -⟩ :=
      BanditAlgorithm.mdp_compact_confidence_optimistic_bellman_solution hS0
        (Nat.pos_of_ne_zero (NeZero.ne A)) r hr (C h t)
        (fun x a ↦ (hball x a).1) (fun x a ↦ (hball x a).2)
        (fun x a p hp ↦ ⟨hp.1, hp.2.1⟩) M hMr hDne
        (fun x a ↦ hgd _ (by have := phaseStart_le (h := h) t; omega) x a)
    exact ⟨ρ, w, f, q, h1, h2, h4, h5, h6⟩
  -- the span of the bias is at most the diameter whenever the switch is on
  have hspan : ∀ (h : MDPTrajectory S A n) (t : ℕ), Gd h t →
      ∀ x y, v h t x - v h t y ≤ D := by
    intro h t hgd x y
    exact BanditAlgorithm.mdp_optimistic_bias_span_le_diameter hS0 M r hMr hD (C h t)
      (fun s a ↦ hgd _ (by have := phaseStart_le (h := h) t; omega) s a) (hplan h t hgd) x y
  -- the increments are bounded by the diameter
  have hbdd : ∀ (t : ℕ) (h : MDPTrajectory S A n) (s' : Fin S), |G h t s'| ≤ D := by
    intro t h s'
    simp only [hGdef]
    by_cases ht : t < n
    · rw [dif_pos ht]
      by_cases hgd : Gd h t
      · rw [if_pos hgd]
        have hP0 : ∀ s'', (0 : ℝ) ≤ ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) :=
          fun s'' ↦ (M.P _ _ s'').coe_nonneg
        have hP1 : ∑ s'', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) = 1 := by
          rw [← NNReal.coe_sum, M.P_sum_one]; simp
        have hrewrite : (∑ s'', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) * v h t s'')
              - v h t s'
            = ∑ s'', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) * (v h t s'' - v h t s') := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1, one_mul]
        rw [hrewrite]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ s'', |((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) * (v h t s'' - v h t s')|
            ≤ ∑ s'', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) * D := by
              refine Finset.sum_le_sum fun s'' _ ↦ ?_
              rw [abs_mul, abs_of_nonneg (hP0 s'')]
              refine mul_le_mul_of_nonneg_left ?_ (hP0 s'')
              exact abs_le.2 ⟨by linarith [hspan h t hgd s' s''], hspan h t hgd s'' s'⟩
          _ = D := by rw [← Finset.sum_mul, hP1, one_mul]
      · rw [if_neg hgd, abs_zero]; linarith
    · rw [dif_neg ht, abs_zero]; linarith
  -- the increments are centred
  have hcent : ∀ (t : ℕ) (ht : t < n) (h : MDPTrajectory S A n),
      ∑ s', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s' : ℝ)) * G h t s' = 0 := by
    intro t ht h
    have hP1 : ∑ s'', ((M.P (h ⟨t, ht⟩).1 (h ⟨t, ht⟩).2 s'' : ℝ)) = 1 := by
      rw [← NNReal.coe_sum, M.P_sum_one]; simp
    simp only [hGdef, dif_pos ht]
    by_cases hgd : Gd h t
    · simp only [if_pos hgd, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1, one_mul]
      ring
    · simp [hgd]
  -- the increments only look at the rounds already played
  have hdep : ∀ (t : ℕ) (h h' : MDPTrajectory S A n),
      (∀ i : Fin n, i.val ≤ t → h i = h' i) → G h t = G h' t := by
    intro t h h' hag
    have hτ : ∀ u ≤ t, mdpPhaseStart h u = mdpPhaseStart h' u := phaseStart_congr hag
    have hC : C h t = C h' t := by
      by_cases ht : t ≤ t
      · funext x a
        simp only [hCdef]
        have hle : mdpPhaseStart h' t ≤ t := phaseStart_le t
        rw [hτ t le_rfl]
        exact confidenceSet_congr hag (by omega) n δ x a
      · omega
    have hGdeq : Gd h t = Gd h' t := by
      simp only [hGddef]
      apply propext
      constructor
      · intro hh k hk x a
        rw [← confidenceSet_congr hag hk n δ x a]; exact hh k hk x a
      · intro hh k hk x a
        rw [confidenceSet_congr hag hk n δ x a]; exact hh k hk x a
    funext s'
    simp only [hGdef, hvdef, hC, hGdeq]
    by_cases ht : t < n
    · rw [dif_pos ht, dif_pos ht, hag ⟨t, ht⟩ le_rfl]
    · rw [dif_neg ht, dif_neg ht]
  -- the Azuma inequality along the trajectory
  have hazuma := BanditAlgorithm.mdp_trajectory_azuma_of_centered_bounded_increments
    n M μ0 (ucrl2Policy n δ r) G D (le_of_lt hD0) hdep hcent hbdd hε0
  refine ⟨{h | ¬ ∃ (st : ℕ → Fin S) (act : ℕ → Fin A),
      (∀ t : Fin n, h t = (st t, act t)) ∧
      ε ≤ ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1))}, ?_, ?_⟩
  · -- the deviation event is small
    have hcompl : ({h : MDPTrajectory S A n | ¬ ∃ (st : ℕ → Fin S) (act : ℕ → Fin A),
        (∀ t : Fin n, h t = (st t, act t)) ∧
        ε ≤ ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1))})ᶜ
        = {h | ∃ (st : ℕ → Fin S) (act : ℕ → Fin A),
            (∀ t : Fin n, h t = (st t, act t)) ∧
            ε ≤ ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1))} := by
      ext h; simp
    rw [hcompl]
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · -- with a single round the sum is empty and the deviation is positive
      have hempty : {h : MDPTrajectory S A n | ∃ (st : ℕ → Fin S) (act : ℕ → Fin A),
          (∀ t : Fin n, h t = (st t, act t)) ∧
          ε ≤ ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1))} = ∅ := by
        ext h
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨st, act, -, hle⟩
        rw [show n - 1 = 0 by omega] at hle
        simp only [Finset.range_zero, Finset.sum_empty] at hle
        have : 0 < ε := by
          refine mul_pos hD0 (Real.sqrt_pos.2 ?_)
          have : (1 : ℝ) ≤ (n : ℝ) := hnR
          nlinarith
        linarith
      rw [hempty]
      simp
    · -- otherwise Azuma applies
      have hnm1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        linarith
      have hεsq : ε ^ 2 = D ^ 2 * (2 * (n : ℝ) * L) := by
        rw [hεdef, mul_pow, Real.sq_sqrt hrad]
      have hkey : Real.exp (-ε ^ 2 / (2 * ((n : ℝ) - 1) * D ^ 2)) ≤ δ / 2 := by
        rw [← hexpL]
        refine Real.exp_le_exp.2 ?_
        rw [hεsq]
        rw [div_le_iff₀ (by positivity)]
        have hDsq : (0 : ℝ) < D ^ 2 := by positivity
        nlinarith [mul_pos hL0 hDsq, mul_nonneg (le_of_lt hL0) (le_of_lt hDsq)]
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by linarith)]
      calc (mdpMeasure M μ0 (ucrl2Policy n δ r) n
              {h | ∃ (st : ℕ → Fin S) (act : ℕ → Fin A),
                (∀ t : Fin n, h t = (st t, act t)) ∧
                ε ≤ ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1))}).toReal
          ≤ Real.exp (-ε ^ 2 / (2 * ((n : ℝ) - 1) * D ^ 2)) := hazuma
        _ ≤ δ / 2 := hkey
  · -- on the confidence event the stopped sum is the true one
    rintro h ⟨hgood, hE⟩ st act hsa
    simp only [Set.mem_setOf_eq, not_exists, not_and] at hE
    have hlt : ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1)) < ε := by
      by_contra hcon
      exact hE st act hsa (le_of_not_gt hcon)
    have hGood_all : ∀ t : ℕ, t < n - 1 → Gd h t := by
      intro t htn k hk x a
      exact hgood k (by omega) x a
    have hsum : ∑ t ∈ Finset.range (n - 1), G h t (st (t + 1))
        = ∑ t ∈ Finset.range (n - 1),
            ((∑ s', (M.P (st t) (act t) s' : ℝ) * v h t s') - v h t (st (t + 1))) := by
      refine Finset.sum_congr rfl fun t hti ↦ ?_
      have htn : t < n - 1 := Finset.mem_range.1 hti
      have ht : t < n := by omega
      simp only [hGdef, dif_pos ht, if_pos (hGood_all t htn)]
      rw [hsa ⟨t, ht⟩]
    rw [hsum] at hlt
    exact le_of_lt (lt_of_lt_of_le hlt (le_of_eq rfl))
