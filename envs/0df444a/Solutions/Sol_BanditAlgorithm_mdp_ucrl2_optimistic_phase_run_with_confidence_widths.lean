-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_optimistic_phase_run_with_confidence_widths
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T23:14:39.837705+00:00
-- url     : https://prove2.me/submissions/bbc8c23e-5a5f-4d27-a1ff-a89f5118f8d8

import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_phase_schedule_from_doubling_rule
import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_action_realisation_ae
import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_bias_martingale_deviation
import Theorems.Thm_BanditAlgorithm_mdp_compact_confidence_optimistic_bellman_solution
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_le_of_bellman_ineq
import Theorems.Thm_BanditAlgorithm_mdp_span_le_gain_mul_diameter
import Theorems.Thm_BanditAlgorithm_prob_vector_l1_ball_nonempty_isCompact

open MeasureTheory ProbabilityTheory ENNReal Finset

namespace UCRL2Run

open BanditAlgorithm

variable {S A n : ℕ}

/-- The empirical transition row is a probability vector, whatever the history:
before any transition has been observed it is the point mass at `s`, and
afterwards the vector of observed frequencies. -/
lemma empiricalRow_isProb (h : MDPTrajectory S A n) (k : ℕ) (s : Fin S) (a : Fin A) :
    (∀ s', 0 ≤ mdpEmpiricalRow h k s a s') ∧ ∑ s', mdpEmpiricalRow h k s a s' = 1 := by
  classical
  by_cases hz : mdpObservedCount h k s a = 0
  · refine ⟨fun s' ↦ ?_, ?_⟩
    · simp only [mdpEmpiricalRow, if_pos hz]
      split <;> norm_num
    · simp only [mdpEmpiricalRow, if_pos hz]
      simp
  · have hzR : (0 : ℝ) < (mdpObservedCount h k s a : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hz
    refine ⟨fun s' ↦ ?_, ?_⟩
    · simp only [mdpEmpiricalRow, if_neg hz]
      positivity
    · simp only [mdpEmpiricalRow, if_neg hz]
      rw [← Finset.sum_div, ← Nat.cast_sum]
      exact div_self hzR.ne'

/-- Every visit strictly before time `k` has its successor state recorded, so the
sample size of the confidence ball read at time `k + 1` is exactly the number of
visits strictly before `k`. -/
lemma observedCount_succ_eq_visitCount (h : MDPTrajectory S A n) (k : ℕ) (hk : k + 1 ≤ n)
    (s : Fin S) (a : Fin A) :
    mdpObservedCount h (k + 1) s a = mdpVisitCount h k s a := by
  classical
  simp only [mdpObservedCount, mdpTransitionCount, mdpVisitCount, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hik : i.val < k
  · have hlt : i.val + 1 < n := by omega
    have hsucc : mdpSuccessor h i = some (h ⟨i.val + 1, hlt⟩).1 := by
      simp only [mdpSuccessor, dif_pos hlt]
    rw [Finset.sum_eq_single (h ⟨i.val + 1, hlt⟩).1]
    · by_cases hc : h i = (s, a)
      · rw [if_pos (show i.val + 1 < k + 1 ∧ h i = (s, a) ∧
            mdpSuccessor h i = some (h ⟨i.val + 1, hlt⟩).1 from ⟨by omega, hc, hsucc⟩),
          if_pos (show i.val < k ∧ h i = (s, a) from ⟨hik, hc⟩)]
      · rw [if_neg (show ¬(i.val + 1 < k + 1 ∧ h i = (s, a) ∧
            mdpSuccessor h i = some (h ⟨i.val + 1, hlt⟩).1) by tauto),
          if_neg (show ¬(i.val < k ∧ h i = (s, a)) by tauto)]
    · intro b _ hb
      refine if_neg ?_
      rintro ⟨-, -, hs⟩
      rw [hsucc] at hs
      exact hb (Option.some_injective _ hs).symm
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  · rw [if_neg (show ¬(i.val < k ∧ h i = (s, a)) by tauto)]
    refine Finset.sum_eq_zero fun s' _ ↦ if_neg ?_
    rintro ⟨h1, -, -⟩
    omega

/-- Visit counts increase with time. -/
lemma visitCount_mono (h : MDPTrajectory S A n) {u w : ℕ} (huw : u ≤ w)
    (s : Fin S) (a : Fin A) : mdpVisitCount h u s a ≤ mdpVisitCount h w s a := by
  classical
  refine Finset.card_le_card fun i hi ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 huw, hi.2⟩

/-- Summing a function of the pair played over the rounds before time `w` is the
same as summing it against the visit counts at time `w`. -/
lemma sum_range_eq_sum_visitCount (h : MDPTrajectory S A n)
    (st : ℕ → Fin S) (act : ℕ → Fin A) (hst : ∀ t : Fin n, h t = (st t, act t))
    (g : Fin S → Fin A → ℝ) {w : ℕ} (hw : w ≤ n) :
    ∑ t ∈ Finset.range w, g (st t) (act t)
      = ∑ s, ∑ a, (mdpVisitCount h w s a : ℝ) * g s a := by
  classical
  induction w with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      refine (Finset.sum_eq_zero fun s _ ↦ Finset.sum_eq_zero fun a _ ↦ ?_).symm
      have : mdpVisitCount h 0 s a = 0 := by
        simp [mdpVisitCount, Finset.filter_eq_empty_iff]
      rw [this]
      simp
  | succ w ih =>
      have hwn : w < n := by omega
      have hstep : ∀ (s : Fin S) (a : Fin A),
          mdpVisitCount h (w + 1) s a
            = mdpVisitCount h w s a + (if h ⟨w, hwn⟩ = (s, a) then 1 else 0) := by
        intro s a
        simp only [mdpVisitCount, Finset.card_filter]
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        have hsplit : (Finset.univ.filter fun i : Fin n ↦ i.val < w + 1 ∧ h i = (s, a))
            = (Finset.univ.filter fun i : Fin n ↦ i.val < w ∧ h i = (s, a))
              ∪ (Finset.univ.filter fun i : Fin n ↦ i.val = w ∧ h i = (s, a)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          constructor
          · rintro ⟨h1, h2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h3 | h3
            · exact Or.inl ⟨h3, h2⟩
            · exact Or.inr ⟨h3, h2⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨by omega, h2⟩
            · exact ⟨by omega, h2⟩
        have hdisj : Disjoint
            (Finset.univ.filter fun i : Fin n ↦ i.val < w ∧ h i = (s, a))
            (Finset.univ.filter fun i : Fin n ↦ i.val = w ∧ h i = (s, a)) := by
          refine Finset.disjoint_left.mpr fun i hi hj ↦ ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
          omega
        rw [hsplit, Finset.sum_union hdisj]
        congr 1
        have hlast : (Finset.univ.filter fun i : Fin n ↦ i.val = w ∧ h i = (s, a))
            = if h ⟨w, hwn⟩ = (s, a) then {(⟨w, hwn⟩ : Fin n)} else ∅ := by
          ext i
          by_cases hc : h ⟨w, hwn⟩ = (s, a)
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc,
              Finset.mem_singleton]
            constructor
            · rintro ⟨h1, -⟩; exact Fin.ext h1
            · rintro rfl; exact ⟨rfl, hc⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc,
              Finset.notMem_empty, iff_false]
            rintro ⟨h1, h2⟩
            exact hc (by rw [show (⟨w, hwn⟩ : Fin n) = i from (Fin.ext h1).symm]; exact h2)
        rw [hlast]
        by_cases hc : h ⟨w, hwn⟩ = (s, a) <;> simp [hc]
      rw [Finset.sum_range_succ, ih (by omega)]
      have : ∑ s, ∑ a, (mdpVisitCount h (w + 1) s a : ℝ) * g s a
          = (∑ s, ∑ a, (mdpVisitCount h w s a : ℝ) * g s a)
            + ∑ s, ∑ a, (if h ⟨w, hwn⟩ = (s, a) then (1 : ℝ) else 0) * g s a := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [hstep s a]
        push_cast
        ring
      rw [this]
      congr 1
      have hpair : h ⟨w, hwn⟩ = (st w, act w) := hst ⟨w, hwn⟩
      rw [hpair]
      symm
      rw [Finset.sum_eq_single (st w)]
      · rw [Finset.sum_eq_single (act w)]
        · simp
        · intro b _ hb
          simp [Prod.ext_iff, Ne.symm hb]
        · intro hb
          exact absurd (Finset.mem_univ _) hb
      · intro b _ hb
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        simp [Prod.ext_iff, Ne.symm hb]
      · intro hb
        exact absurd (Finset.mem_univ _) hb

end UCRL2Run

open UCRL2Run BanditAlgorithm

/-- The run of UCRL2 realises an optimistic phase run reporting its confidence
widths.  The policy is `ucrl2Policy`, which depends only on the known `n`, `δ`
and `r`; the event `E` is the intersection of the martingale event with the
full-measure set on which the actions are the ones the policy prescribes. -/
theorem solution
    (S A n : ℕ) (hS : 2 ≤ S) (hA : 0 < A) (hn : 0 < n)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ π : MDPPolicy S A,
      ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating → 1 ≤ mdpDiameter M →
        ∀ μ0 : MDPStateDistribution S,
          ∃ E : Set (MDPTrajectory S A n),
            mdpMeasure M μ0 π n Eᶜ ≤ ENNReal.ofReal (δ / 2) ∧
            ∀ h ∈ mdpConfidenceGoodEvent M n δ ∩ E,
            ∃ (st : ℕ → Fin S) (act : ℕ → Fin A) (K : ℕ) (τ : ℕ → ℕ)
              (ρ : ℕ → ℝ) (v : ℕ → Fin S → ℝ) (q : ℕ → Fin S → Fin S → ℝ)
              (N ν : ℕ → Fin S → Fin A → ℝ),
              (∀ t : Fin n, h t = (st t, act t)) ∧
              τ 0 = 0 ∧ τ K = n ∧ (∀ k, τ k ≤ τ (k + 1)) ∧
              (K : ℝ) ≤ 3 * Real.sqrt (S * A * n) ∧
              (∀ k < K, mdpOptimalGain M ≤ ρ k) ∧
              (∀ k < K, ∀ x y : Fin S, v k x - v k y ≤ mdpDiameter M) ∧
              (∀ k < K, ∀ s : Fin S, ∑ s', q k s s' = 1) ∧
              (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ρ k + v k (st t)
                  = M.r (st t) (act t) + ∑ s', q k (st t) s' * v k s') ∧
              (∀ s a, N 0 s a = 0) ∧
              (∀ k s a, 0 ≤ ν k s a) ∧
              (∀ k s a, N (k + 1) s a = N k s a + ν k s a) ∧
              (∀ k s a, ν k s a ≤ max 1 (N k s a)) ∧
              (∑ s, ∑ a, N K s a ≤ (n : ℝ)) ∧
              (∀ k < K, ∀ g : Fin S → Fin A → ℝ,
                ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), g (st t) (act t)
                  = ∑ s, ∑ a, ν k s a * g s a) ∧
              (∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                ∑ s', |q k (st t) s' - (M.P (st t) (act t) s' : ℝ)|
                  ≤ 2 * Real.sqrt (14 * S * Real.log (2 * S * A * n / δ)
                      / max 1 (N k (st t) (act t)))) ∧
              (∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
                  ((∑ s', (M.P (st t) (act t) s' : ℝ) * v k s') - v k (st (t + 1)))
                ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ))) := by
  classical
  haveI : NeZero A := ⟨hA.ne'⟩
  have hS0 : 0 < S := lt_of_lt_of_le (by norm_num) hS
  obtain ⟨hδ0, hδ1⟩ := hδ
  refine ⟨ucrl2Policy n δ r, ?_⟩
  intro M hMr hMcomm hD μ0
  have hMDne : mdpDiameterENN M ≠ ⊤ := by
    intro htop
    rw [show mdpDiameter M = (mdpDiameterENN M).toReal from rfl, htop] at hD
    simp only [ENNReal.toReal_top] at hD
    linarith
  have hD0 : (0 : ℝ) ≤ mdpDiameter M := le_trans zero_le_one hD
  obtain ⟨ED, hEDprob, hEDsum⟩ :=
    BanditAlgorithm.mdp_ucrl2_bias_martingale_deviation S A n hS hn δ ⟨hδ0, hδ1⟩ r hr M hMr hD μ0
  set R : Set (MDPTrajectory S A n) :=
    {h : MDPTrajectory S A n | ∀ t : Fin n,
      (h t).2 = mdpOptimisticActionMap r
        (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t.val + 1) n δ x a) (h t).1} with hRdef
  have hR0 : mdpMeasure M μ0 (ucrl2Policy n δ r) n Rᶜ = 0 :=
    BanditAlgorithm.mdp_ucrl2_action_realisation_ae S A n δ r M μ0
  refine ⟨ED ∩ R, ?_, ?_⟩
  · rw [Set.compl_inter]
    refine le_trans (measure_union_le _ _) ?_
    rw [hR0, add_zero]
    exact hEDprob
  intro h hh
  have hgood : h ∈ mdpConfidenceGoodEvent M n δ := hh.1
  have hEDmem : h ∈ ED := hh.2.1
  have hRmem : ∀ t : Fin n, (h t).2 = mdpOptimisticActionMap r
      (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t.val + 1) n δ x a) (h t).1 := hh.2.2
  obtain ⟨K, τ, hτ0, hτK, hτmono, hτlt, hτge, hK, hphase, hdouble⟩ :=
    BanditAlgorithm.mdp_ucrl2_phase_schedule_from_doubling_rule S A n hS0 hA hn h
  have hτmono' : Monotone τ := monotone_nat_of_le_succ hτmono
  set Cf : ℕ → Fin S → Fin A → Set (Fin S → ℝ) :=
    fun k x a ↦ mdpConfidenceSet h (τ k + 1) n δ x a with hCfdef
  have hτlen : ∀ k, k < K → τ k + 1 ≤ n := by
    intro k hk
    have h1 : τ (k + 1) ≤ τ K := hτmono' (by omega)
    have h2 := hτlt k hk
    omega
  have hMC : ∀ k < K, ∀ (s : Fin S) (a : Fin A),
      (fun s' ↦ ((M.P s a s' : ℝ))) ∈ Cf k s a := fun k hk s a ↦
    hgood (τ k + 1) (hτlen k hk) s a
  have hCprob : ∀ k, ∀ (s : Fin S) (a : Fin A), ∀ p ∈ Cf k s a,
      (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1 := fun _ _ _ _ hp ↦ ⟨hp.1, hp.2.1⟩
  have hball : ∀ k (s : Fin S) (a : Fin A),
      (∃ p : Fin S → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
          ∑ i, |p i - mdpEmpiricalRow h (τ k + 1) s a i|
            ≤ mdpConfidenceRadius S A n δ (mdpObservedCount h (τ k + 1) s a)) ∧
        IsCompact {p : Fin S → ℝ | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
          ∑ i, |p i - mdpEmpiricalRow h (τ k + 1) s a i|
            ≤ mdpConfidenceRadius S A n δ (mdpObservedCount h (τ k + 1) s a)} := by
    intro k s a
    exact BanditAlgorithm.prob_vector_l1_ball_nonempty_isCompact
      (mdpEmpiricalRow h (τ k + 1) s a) (empiricalRow_isProb h (τ k + 1) s a).1
      (empiricalRow_isProb h (τ k + 1) s a).2 _ (Real.sqrt_nonneg _)
  have hCne : ∀ k, ∀ (s : Fin S) (a : Fin A), (Cf k s a).Nonempty := by
    intro k s a
    obtain ⟨p, hp⟩ := (hball k s a).1
    exact ⟨p, hp⟩
  have hCcomp : ∀ k, ∀ (s : Fin S) (a : Fin A), IsCompact (Cf k s a) :=
    fun k s a ↦ (hball k s a).2
  have hplan : ∀ k < K, IsOptimisticPlan r (Cf k)
      (mdpOptimisticGain r (Cf k)) (mdpOptimisticBias r (Cf k))
      (mdpOptimisticActionMap r (Cf k)) (mdpOptimisticRow r (Cf k)) := by
    intro k hk
    refine isOptimisticPlan_mdpOptimisticPlan r (Cf k) ?_
    obtain ⟨ρ', v', f', q', h1, h2, -, h4, h5, h6, -⟩ :=
      BanditAlgorithm.mdp_compact_confidence_optimistic_bellman_solution hS0 hA r hr
        (Cf k) (hCne k) (hCcomp k) (hCprob k) M hMr hMDne (hMC k hk)
    exact ⟨ρ', v', f', q', h1, h2, h4, h5, h6⟩
  set Blast : Fin S → ℝ :=
    mdpOptimisticBias r (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h (n - 1) + 1) n δ x a)
    with hBlastdef
  obtain ⟨smax, -, hsmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin S)) Blast ⟨⟨0, hS0⟩, Finset.mem_univ _⟩
  set st : ℕ → Fin S := fun t ↦ if ht : t < n then (h ⟨t, ht⟩).1 else smax with hstdef
  set act : ℕ → Fin A := fun t ↦ if ht : t < n then (h ⟨t, ht⟩).2 else default with hactdef
  have hstact : ∀ t : Fin n, h t = (st t, act t) := by
    intro t
    simp only [hstdef, hactdef, dif_pos t.isLt, Fin.eta]
  have hact_eq : ∀ k < K, ∀ t ∈ Finset.Ico (τ k) (τ (k + 1)),
      act t = mdpOptimisticActionMap r (Cf k) (st t) := by
    intro k hk t ht
    have htn : t < n := by
      have h1 := Finset.mem_Ico.mp ht
      have h2 : τ (k + 1) ≤ n := by rw [← hτK]; exact hτmono' (by omega)
      omega
    have hr' := hRmem ⟨t, htn⟩
    simp only [hphase k hk t ht] at hr'
    simp only [hstdef, hactdef, dif_pos htn]
    exact hr'
  refine ⟨st, act, K, τ,
    fun k ↦ mdpOptimisticGain r (Cf k),
    fun k ↦ mdpOptimisticBias r (Cf k),
    fun k ↦ mdpOptimisticRow r (Cf k),
    fun k s a ↦ (mdpVisitCount h (τ k) s a : ℝ),
    fun k s a ↦ (mdpVisitCount h (τ (k + 1)) s a : ℝ) - (mdpVisitCount h (τ k) s a : ℝ),
    hstact, hτ0, hτK, hτmono, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- optimism
    intro k hk
    obtain ⟨-, -, hp3, -, -⟩ := hplan k hk
    obtain ⟨lo, -, hlo⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin S))
      (mdpOptimisticBias r (Cf k)) ⟨⟨0, hS0⟩, Finset.mem_univ _⟩
    obtain ⟨hi, -, hhi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin S))
      (mdpOptimisticBias r (Cf k)) ⟨⟨0, hS0⟩, Finset.mem_univ _⟩
    refine BanditAlgorithm.mdp_optimal_gain_le_of_bellman_ineq hS0 hA M _
      (mdpOptimisticBias r (Cf k)) (mdpOptimisticBias r (Cf k) lo)
      (mdpOptimisticBias r (Cf k) hi)
      (fun s ↦ ⟨hlo s (Finset.mem_univ _), hhi s (Finset.mem_univ _)⟩) ?_
    intro s a
    rw [hMr]
    exact hp3 s a _ (hMC k hk s a)
  · -- span
    intro k hk x y
    obtain ⟨hp1, hp2, hp3, -, -⟩ := hplan k hk
    obtain ⟨lo, -, hlo⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin S))
      (mdpOptimisticBias r (Cf k)) ⟨⟨0, hS0⟩, Finset.mem_univ _⟩
    obtain ⟨hi, -, hhi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin S))
      (mdpOptimisticBias r (Cf k)) ⟨⟨0, hS0⟩, Finset.mem_univ _⟩
    have hspan := BanditAlgorithm.mdp_span_le_gain_mul_diameter M _ hp1
      (mdpOptimisticBias r (Cf k)) (mdpOptimisticBias r (Cf k) lo)
      (mdpOptimisticBias r (Cf k) hi)
      (fun s ↦ ⟨hlo s (Finset.mem_univ _), hhi s (Finset.mem_univ _)⟩)
      (by intro s a; rw [hMr]; exact hp3 s a _ (hMC k hk s a)) hMDne x y
    nlinarith [hspan, hp2, hD0]
  · -- optimistic rows are probability vectors
    intro k hk s
    obtain ⟨-, -, -, hp4, -⟩ := hplan k hk
    exact (hp4 s).2.1
  · -- Bellman equation along the realised trajectory
    intro k hk t ht
    obtain ⟨-, -, -, -, hp5⟩ := hplan k hk
    rw [hMr, hact_eq k hk t ht]
    exact hp5 (st t)
  · -- the counts start at zero
    intro s a
    have h0 : mdpVisitCount h 0 s a = 0 := by simp [mdpVisitCount]
    simp only [hτ0, h0, Nat.cast_zero]
  · -- the phase counts are nonnegative
    intro k s a
    have h1 : mdpVisitCount h (τ k) s a ≤ mdpVisitCount h (τ (k + 1)) s a :=
      visitCount_mono h (hτmono k) s a
    have h2 : (mdpVisitCount h (τ k) s a : ℝ) ≤ (mdpVisitCount h (τ (k + 1)) s a : ℝ) := by
      exact_mod_cast h1
    linarith
  · -- the counts accumulate
    intro k s a
    ring
  · -- the doubling inequality
    intro k s a
    by_cases hk : k < K
    · have hd := hdouble k hk s a
      have hd' : ((mdpVisitCount h (τ (k + 1)) s a : ℕ) : ℝ)
          ≤ (mdpVisitCount h (τ k) s a : ℝ)
            + ((max 1 (mdpVisitCount h (τ k) s a) : ℕ) : ℝ) := by
        exact_mod_cast hd
      rw [Nat.cast_max, Nat.cast_one] at hd'
      linarith
    · have h1 : τ k = n := hτge k (by omega)
      have h2 : τ (k + 1) = n := hτge (k + 1) (by omega)
      show (mdpVisitCount h (τ (k + 1)) s a : ℝ) - (mdpVisitCount h (τ k) s a : ℝ)
        ≤ max 1 ((mdpVisitCount h (τ k) s a : ℝ))
      rw [h1, h2, sub_self]
      exact le_trans zero_le_one (le_max_left _ _)
  · -- the total number of visits is the horizon
    have hsum := sum_range_eq_sum_visitCount h st act hstact (fun _ _ ↦ (1 : ℝ)) (le_refl n)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
    show (∑ s, ∑ a, (mdpVisitCount h (τ K) s a : ℝ)) ≤ (n : ℝ)
    rw [hτK, ← hsum]
  · -- summing over a phase is summing against the phase counts
    intro k hk g
    have hkn : τ (k + 1) ≤ n := by rw [← hτK]; exact hτmono' (by omega)
    have h1 := sum_range_eq_sum_visitCount h st act hstact g hkn
    have h2 := sum_range_eq_sum_visitCount h st act hstact g (le_trans (hτmono k) hkn)
    rw [Finset.sum_Ico_eq_sub _ (hτmono k), h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  · -- the confidence width of the pair played
    intro k hk t ht
    obtain ⟨-, -, -, hp4, -⟩ := hplan k hk
    have hqmem := hp4 (st t)
    rw [← hact_eq k hk t ht] at hqmem
    have hPmem := hMC k hk (st t) (act t)
    have hobs : mdpObservedCount h (τ k + 1) (st t) (act t)
        = mdpVisitCount h (τ k) (st t) (act t) :=
      observedCount_succ_eq_visitCount h (τ k) (hτlen k hk) _ _
    have htri : ∑ s', |mdpOptimisticRow r (Cf k) (st t) s' - (M.P (st t) (act t) s' : ℝ)|
        ≤ 2 * mdpConfidenceRadius S A n δ (mdpObservedCount h (τ k + 1) (st t) (act t)) := by
      calc ∑ s', |mdpOptimisticRow r (Cf k) (st t) s' - (M.P (st t) (act t) s' : ℝ)|
          ≤ ∑ s', (|mdpOptimisticRow r (Cf k) (st t) s'
                - mdpEmpiricalRow h (τ k + 1) (st t) (act t) s'|
              + |mdpEmpiricalRow h (τ k + 1) (st t) (act t) s'
                - (M.P (st t) (act t) s' : ℝ)|) :=
            Finset.sum_le_sum fun s' _ ↦ abs_sub_le _ _ _
        _ = (∑ s', |mdpOptimisticRow r (Cf k) (st t) s'
                - mdpEmpiricalRow h (τ k + 1) (st t) (act t) s'|)
            + ∑ s', |mdpEmpiricalRow h (τ k + 1) (st t) (act t) s'
                - (M.P (st t) (act t) s' : ℝ)| := Finset.sum_add_distrib
        _ ≤ mdpConfidenceRadius S A n δ (mdpObservedCount h (τ k + 1) (st t) (act t))
            + mdpConfidenceRadius S A n δ (mdpObservedCount h (τ k + 1) (st t) (act t)) := by
            refine add_le_add hqmem.2.2 ?_
            simpa only [abs_sub_comm] using hPmem.2.2
        _ = 2 * mdpConfidenceRadius S A n δ
              (mdpObservedCount h (τ k + 1) (st t) (act t)) := by ring
    rw [hobs, mdpConfidenceRadius, Nat.cast_max, Nat.cast_one] at htri
    exact htri
  · -- the martingale term
    set F : ℕ → ℝ := fun t ↦
      (∑ s', (M.P (st t) (act t) s' : ℝ)
          * mdpOptimisticBias r
              (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a) s')
        - mdpOptimisticBias r
            (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t + 1) n δ x a) (st (t + 1))
      with hFdef
    have hcollapse : ∀ m, m ≤ K →
        ∑ k ∈ Finset.range m, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), F t
          = ∑ t ∈ Finset.Ico (τ 0) (τ m), F t := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ih =>
          intro hm
          rw [Finset.sum_range_succ, ih (by omega)]
          exact Finset.sum_Ico_consecutive _ (hτmono' (Nat.zero_le m)) (hτmono m)
    have hlast : F (n - 1) ≤ 0 := by
      have hPsum : ∑ s', ((M.P (st (n - 1)) (act (n - 1)) s' : ℝ)) = 1 := by
        rw [← NNReal.coe_sum, M.P_sum_one]; simp
      have hPnn : ∀ s', (0 : ℝ) ≤ ((M.P (st (n - 1)) (act (n - 1)) s' : ℝ)) :=
        fun s' ↦ (M.P _ _ s').coe_nonneg
      have hle : ∑ s', (M.P (st (n - 1)) (act (n - 1)) s' : ℝ) * Blast s'
          ≤ ∑ s', (M.P (st (n - 1)) (act (n - 1)) s' : ℝ) * Blast smax :=
        Finset.sum_le_sum fun s' _ ↦
          mul_le_mul_of_nonneg_left (hsmax s' (Finset.mem_univ _)) (hPnn s')
      rw [← Finset.sum_mul, hPsum, one_mul] at hle
      have hstn : st n = smax := by simp [hstdef]
      have hnn : n - 1 + 1 = n := by omega
      simp only [hFdef, hnn, hstn, ← hBlastdef]
      linarith
    calc ∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)),
            ((∑ s', (M.P (st t) (act t) s' : ℝ) * mdpOptimisticBias r (Cf k) s')
              - mdpOptimisticBias r (Cf k) (st (t + 1)))
        = ∑ k ∈ Finset.range K, ∑ t ∈ Finset.Ico (τ k) (τ (k + 1)), F t := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          refine Finset.sum_congr rfl fun t ht ↦ ?_
          simp only [hFdef, hphase k (Finset.mem_range.mp hk) t ht, hCfdef]
      _ = ∑ t ∈ Finset.Ico (τ 0) (τ K), F t := hcollapse K le_rfl
      _ = ∑ t ∈ Finset.range n, F t := by rw [hτ0, hτK, Finset.range_eq_Ico]
      _ = (∑ t ∈ Finset.range (n - 1), F t) + F (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          exact Finset.sum_range_succ _ _
      _ ≤ mdpDiameter M * Real.sqrt (2 * n * Real.log (2 / δ)) := by
          have hmg := hEDsum h ⟨hgood, hEDmem⟩ st act hstact
          simp only [← hFdef] at hmg
          linarith
