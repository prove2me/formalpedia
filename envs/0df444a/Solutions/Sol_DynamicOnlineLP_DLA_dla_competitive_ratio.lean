-- Prove2me | solution 1 for DynamicOnlineLP.DLA.dla_competitive_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T07:50:06.348348+00:00
-- url     : https://prove2.me/submissions/8a91025e-abac-4094-b3d7-60fb32d5e94c

import Definitions.Def_DynamicOnlineLP_DLA_Algorithm
import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Theorems.Thm_DynamicOnlineLP_DLA_expected_partialOPT_le
import Theorems.Thm_DynamicOnlineLP_DLA_learned_price_feasible
import Theorems.Thm_DynamicOnlineLP_DLA_learned_price_near_optimal
import Theorems.Thm_DynamicOnlineLP_DLA_phase_sums
import Theorems.Thm_LP_strong_duality_matrix

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.LearnedPrices

theorem eps_pos (E : ℕ) : 0 < eps E := pow_pos (by norm_num) _

theorem eps_le_half {E : ℕ} (hE : 1 ≤ E) : eps E ≤ 1 / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : E ≠ 0)
  unfold eps
  rw [pow_succ]
  have hpow : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem learnLen_mul_pow_eq {n E : ℕ} (hdvd : 2 ^ E ∣ n) :
    learnLen n E * 2 ^ E = n := Nat.div_mul_cancel hdvd

theorem learnLen_pos {n E : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n) :
    0 < learnLen n E := by
  exact Nat.div_pos (Nat.le_of_dvd hn hdvd) (pow_pos (by decide) _)

theorem eps_mul_population_eq_learnLen {n E : ℕ} (hdvd : 2 ^ E ∣ n) :
    eps E * (n : ℝ) = (learnLen n E : ℝ) := by
  have h : (learnLen n E : ℝ) * (2 : ℝ) ^ E = n := by
    exact_mod_cast learnLen_mul_pow_eq hdvd
  have hp : (2 : ℝ) ^ E ≠ 0 := by positivity
  unfold eps
  rw [div_pow, one_pow]
  rw [← h]
  field_simp

theorem phase_time_bounds {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) : 0 < ℓ ∧ 2 * ℓ ≤ n ∧ learnLen n E ≤ ℓ := by
  obtain ⟨k, hk, rfl⟩ := mem_image.mp hℓ
  have hkE : k < E := mem_range.mp hk
  have hlen := learnLen_pos hn hdvd
  have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  refine ⟨mul_pos hlen hpow, ?_, Nat.le_mul_of_pos_right _ hpow⟩
  calc
    2 * (learnLen n E * 2 ^ k) = learnLen n E * 2 ^ (k + 1) := by
      rw [pow_succ]
      ring
    _ ≤ learnLen n E * 2 ^ E :=
      Nat.mul_le_mul_left _ (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))
    _ = n := learnLen_mul_pow_eq hdvd

theorem phase_card_le (n E : ℕ) : (phases n E).card ≤ E := by
  exact (card_image_le).trans_eq (card_range E)

theorem exponent_le_population {n E : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n) : E ≤ n := by
  exact (Nat.le_of_lt (Nat.lt_two_pow_self : E < 2 ^ E)).trans (Nat.le_of_dvd hn hdvd)

theorem two_le_population {n E : ℕ} (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) : 2 ≤ n := by
  have hpow : (2 : ℕ) ≤ 2 ^ E := by
    simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hE
  exact hpow.trans (Nat.le_of_dvd hn hdvd)

theorem phase_ratio_bounds {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) : 0 < (ℓ : ℝ) / n ∧ eps E ≤ (ℓ : ℝ) / n := by
  obtain ⟨hℓpos, _, hlen⟩ := phase_time_bounds hn hdvd hℓ
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨div_pos (by exact_mod_cast hℓpos) hnreal, ?_⟩
  apply (le_div_iff₀ hnreal).mpr
  rw [eps_mul_population_eq_learnLen hdvd]
  exact_mod_cast hlen

theorem phase_slack_sq_ratio {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) :
    (slack n E ℓ) ^ 2 * ((ℓ : ℝ) / n) = (eps E) ^ 2 := by
  have hℓpos := (phase_time_bounds hn hdvd hℓ).1
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hℓreal : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  unfold slack
  rw [mul_pow, Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  field_simp

theorem phase_slack_bounds {n E ℓ : ℕ} (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) (hℓ : ℓ ∈ phases n E) :
    0 < slack n E ℓ ∧ slack n E ℓ ≤ 1 := by
  have hℓpos := (phase_time_bounds hn hdvd hℓ).1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓreal : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hpos : 0 < slack n E ℓ :=
    mul_pos (eps_pos E) (Real.sqrt_pos.mpr (div_pos hnreal hℓreal))
  refine ⟨hpos, ?_⟩
  have hratio := phase_ratio_bounds hn hdvd hℓ
  have heps := eps_pos E
  have hhalf := eps_le_half hE
  have hepssq : (eps E) ^ 2 ≤ eps E := by nlinarith
  have heq := phase_slack_sq_ratio hn hdvd hℓ
  apply le_of_not_gt
  intro hgt
  have hsq : 1 < (slack n E ℓ) ^ 2 := by nlinarith
  have hmul := mul_lt_mul_of_pos_right hsq hratio.1
  rw [one_mul, heq] at hmul
  exact (not_lt_of_ge (hepssq.trans hratio.2)) hmul

theorem phase_budget_identity {n E ℓ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hℓ : ℓ ∈ phases n E) (b : ℝ) :
    (slack n E ℓ) ^ 2 * (((ℓ : ℝ) / n) * b) = (eps E) ^ 2 * b := by
  rw [← mul_assoc, phase_slack_sq_ratio hn hdvd hℓ]

theorem log_population_accuracy_ge_one {n E : ℕ} (hn : 0 < n) (hE : 1 ≤ E)
    (hdvd : 2 ^ E ∣ n) : 1 ≤ Real.log ((n : ℝ) / eps E) := by
  have heps := eps_pos E
  have hhalf := eps_le_half hE
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast two_le_population hn hE hdvd
  have hQ : (4 : ℝ) ≤ (n : ℝ) / eps E := (le_div_iff₀ heps).mpr (by linarith)
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  exact Real.exp_one_lt_three.le.trans (by linarith)

end TCSShortlistDLAMain.LearnedPrices

/-!
Exact time geometry for the canonical Nat.log-based DLA phase selection,
including the post-learning partition and a dyadic telescoping identity.
-/

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.LearnedPrices

/-- The actual canonical phase start is a learning phase whose window contains
the given post-learning time. This includes the exact half-open endpoints. -/
theorem phaseStart_mem_and_bounds {n E τ : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (hτlo : learnLen n E ≤ τ) (hτhi : τ < n) :
    phaseStart n E τ ∈ phases n E ∧
      phaseStart n E τ ≤ τ ∧ τ < 2 * phaseStart n E τ := by
  have hk : 0 < learnLen n E := learnLen_pos hn hdvd
  have hq : 0 < τ / learnLen n E := Nat.div_pos hτlo hk
  have hqE : τ / learnLen n E < 2 ^ E := by
    apply (Nat.div_lt_iff_lt_mul hk).mpr
    rw [Nat.mul_comm, learnLen_mul_pow_eq hdvd]
    exact hτhi
  have hrE : Nat.log 2 (τ / learnLen n E) < E := Nat.log_lt_of_lt_pow hq.ne' hqE
  have hlo : 2 ^ Nat.log 2 (τ / learnLen n E) ≤ τ / learnLen n E :=
    Nat.pow_log_le_self 2 hq.ne'
  have hhi : τ / learnLen n E < 2 ^ (Nat.log 2 (τ / learnLen n E) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) _
  refine ⟨mem_image.mpr ⟨Nat.log 2 (τ / learnLen n E), mem_range.mpr hrE, rfl⟩, ?_, ?_⟩
  · unfold phaseStart
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk).mp hlo
  · unfold phaseStart
    have h := (Nat.div_lt_iff_lt_mul hk).mp hhi
    simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- Every time in a canonical phase window uses exactly that phase's price. -/
theorem phaseStart_eq_of_mem_window {n E ℓ τ : ℕ} (hn : 0 < n)
    (hdvd : 2 ^ E ∣ n) (hℓ : ℓ ∈ phases n E)
    (hlo : ℓ ≤ τ) (hhi : τ < 2 * ℓ) : phaseStart n E τ = ℓ := by
  have hk : 0 < learnLen n E := learnLen_pos hn hdvd
  obtain ⟨r, _, rfl⟩ := mem_image.mp hℓ
  have hlo' : 2 ^ r ≤ τ / learnLen n E := by
    apply (Nat.le_div_iff_mul_le hk).mpr
    simpa only [Nat.mul_comm] using hlo
  have hhi' : τ / learnLen n E < 2 ^ (r + 1) := by
    apply (Nat.div_lt_iff_lt_mul hk).mpr
    simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hhi
  unfold phaseStart
  rw [Nat.log_eq_of_pow_le_of_lt_pow hlo' hhi']

/-- The exact half-open phase windows are pairwise disjoint. -/
theorem phase_windows_pairwiseDisjoint {n E : ℕ} (hn : 0 < n)
    (hdvd : 2 ^ E ∣ n) :
    Set.PairwiseDisjoint (↑(phases n E) : Set ℕ)
      (fun ℓ => Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ)) := by
  intro ℓ hℓ ℓ' hℓ' hne
  apply Finset.disjoint_left.mpr
  intro t ht ht'
  have hstart := phaseStart_eq_of_mem_window hn hdvd hℓ
    (mem_filter.mp ht).2.1 (mem_filter.mp ht).2.2
  have hstart' := phaseStart_eq_of_mem_window hn hdvd hℓ'
    (mem_filter.mp ht').2.1 (mem_filter.mp ht').2.2
  exact hne (hstart.symm.trans hstart')

/-- The phase windows partition exactly the post-learning arrival times. -/
theorem phase_windows_biUnion {n E : ℕ} (hn : 0 < n) (hdvd : 2 ^ E ∣ n) :
    (phases n E).biUnion
        (fun ℓ => Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ)) =
      Finset.univ.filter (fun t : Fin n => learnLen n E ≤ t.val) := by
  ext t
  constructor
  · intro ht
    obtain ⟨ℓ, hℓ, ht⟩ := mem_biUnion.mp ht
    apply mem_filter.mpr
    exact ⟨mem_univ t, (phase_time_bounds hn hdvd hℓ).2.2.trans (mem_filter.mp ht).2.1⟩
  · intro ht
    have hstart := phaseStart_mem_and_bounds hn hdvd (mem_filter.mp ht).2 t.isLt
    apply mem_biUnion.mpr
    exact ⟨phaseStart n E t.val, hstart.1, mem_filter.mpr ⟨mem_univ t, hstart.2⟩⟩

/-- Any real sum supported after learning decomposes over the exact phase windows. -/
theorem sum_eq_sum_phases (n E : ℕ) (hn : 0 < n) (hdvd : 2 ^ E ∣ n)
    (f : Fin n → ℝ) (hf : ∀ t, t.val < learnLen n E → f t = 0) :
    (∑ t : Fin n, f t) =
      ∑ ℓ ∈ phases n E,
        ∑ t ∈ Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ), f t := by
  have hsum :
      (∑ t ∈ Finset.univ.filter (fun t : Fin n => learnLen n E ≤ t.val), f t) =
        ∑ t : Fin n, f t := by
    apply Finset.sum_subset (filter_subset _ _)
    intro t _ ht
    have hnot : ¬learnLen n E ≤ t.val := by
      simpa only [mem_filter, mem_univ, true_and] using ht
    exact hf t (lt_of_not_ge hnot)
  calc
    (∑ t : Fin n, f t) =
        ∑ t ∈ Finset.univ.filter (fun t : Fin n => learnLen n E ≤ t.val), f t := hsum.symm
    _ = ∑ t ∈ (phases n E).biUnion
        (fun ℓ => Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ)), f t := by
      rw [phase_windows_biUnion hn hdvd]
    _ = _ := Finset.sum_biUnion (phase_windows_pairwiseDisjoint hn hdvd)

/-- Consecutive differences telescope over the canonical dyadic learning phases.
No monotonicity or sign assumption on the arbitrary sequence is needed. -/
theorem dyadic_telescope (n E : ℕ) (hn : 0 < n) (hdvd : 2 ^ E ∣ n) (V : ℕ → ℝ) :
    (∑ ℓ ∈ phases n E, (V (2 * ℓ) - V ℓ)) = V n - V (learnLen n E) := by
  have hk : 0 < learnLen n E := learnLen_pos hn hdvd
  have hinj : Function.Injective (fun r : ℕ => learnLen n E * 2 ^ r) := by
    intro r s h
    exact (Nat.pow_right_inj (by decide : 1 < (2 : ℕ))).mp (Nat.mul_left_cancel hk h)
  unfold phases
  rw [Finset.sum_image hinj.injOn]
  have hstep (r : ℕ) : 2 * (learnLen n E * 2 ^ r) = learnLen n E * 2 ^ (r + 1) := by
    rw [pow_succ]
    ring
  calc
    (∑ r ∈ range E, (V (2 * (learnLen n E * 2 ^ r)) - V (learnLen n E * 2 ^ r))) =
        ∑ r ∈ range E, (V (learnLen n E * 2 ^ (r + 1)) - V (learnLen n E * 2 ^ r)) := by
      simp_rw [hstep]
    _ = V (learnLen n E * 2 ^ E) - V (learnLen n E * 2 ^ 0) :=
      Finset.sum_range_sub (fun r => V (learnLen n E * 2 ^ r)) E
    _ = V n - V (learnLen n E) := by
      rw [learnLen_mul_pow_eq hdvd]
      simp only [pow_zero, mul_one]

end TCSShortlistDLAMain.LearnedPrices

/-!
Bounds and prefix identities for the canonical guarded DLA recursion. The total-proposal
load premise in the no-rejection lemma is an internal conditional interface; the main
theorem supplies it from its simultaneous learned-price event.
-/

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.DLAExecution

theorem threshold_mem_Icc {ι : Type} {m : ℕ} (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (p : Fin m → ℝ) (t : ι) :
    0 ≤ threshold π a p t ∧ threshold π a p t ≤ 1 := by
  classical
  unfold threshold
  split_ifs <;> norm_num

variable {m n : ℕ} (I : Instance m n) (rule : DualRule m n) (E : ℕ)
  (σ : Equiv.Perm (Fin n))

theorem dlaProposal_mem_Icc (t : Fin n) :
    0 ≤ dlaProposal I rule E σ t ∧ dlaProposal I rule E σ t ≤ 1 := by
  unfold dlaProposal
  split_ifs
  · exact ⟨le_rfl, zero_le_one⟩
  · exact threshold_mem_Icc _ _ _ _

theorem dlaProposal_nonneg (t : Fin n) : 0 ≤ dlaProposal I rule E σ t :=
  (dlaProposal_mem_Icc I rule E σ t).1

theorem dlaProposal_le_one (t : Fin n) : dlaProposal I rule E σ t ≤ 1 :=
  (dlaProposal_mem_Icc I rule E σ t).2

theorem dlaProposal_eq_zero_of_lt_learnLen (t : Fin n) (ht : t.val < learnLen n E) :
    dlaProposal I rule E σ t = 0 := by
  simp only [dlaProposal, if_pos ht]

theorem dlaDecision_mem_Icc (used : Fin m → ℝ) (t : Fin n) :
    0 ≤ dlaDecision I rule E σ used t ∧ dlaDecision I rule E σ used t ≤ 1 := by
  classical
  unfold dlaDecision
  split_ifs
  · exact dlaProposal_mem_Icc I rule E σ t
  · exact ⟨le_rfl, zero_le_one⟩

theorem dlaDecision_nonneg (used : Fin m → ℝ) (t : Fin n) :
    0 ≤ dlaDecision I rule E σ used t := (dlaDecision_mem_Icc I rule E σ used t).1

theorem dlaDecision_le_one (used : Fin m → ℝ) (t : Fin n) :
    dlaDecision I rule E σ used t ≤ 1 := (dlaDecision_mem_Icc I rule E σ used t).2

theorem dlaDecision_le_proposal (used : Fin m → ℝ) (t : Fin n) :
    dlaDecision I rule E σ used t ≤ dlaProposal I rule E σ t := by
  classical
  unfold dlaDecision
  split_ifs
  · exact le_rfl
  · exact dlaProposal_nonneg I rule E σ t

theorem dlaX_mem_Icc (t : Fin n) : 0 ≤ dlaX I rule E σ t ∧ dlaX I rule E σ t ≤ 1 :=
  dlaDecision_mem_Icc I rule E σ (dlaUsed I rule E σ t.val) t

theorem dlaX_nonneg (t : Fin n) : 0 ≤ dlaX I rule E σ t :=
  (dlaX_mem_Icc I rule E σ t).1

theorem dlaX_le_one (t : Fin n) : dlaX I rule E σ t ≤ 1 :=
  (dlaX_mem_Icc I rule E σ t).2

theorem dlaX_le_proposal (t : Fin n) : dlaX I rule E σ t ≤ dlaProposal I rule E σ t :=
  dlaDecision_le_proposal I rule E σ (dlaUsed I rule E σ t.val) t

theorem dlaX_eq_zero_of_lt_learnLen (t : Fin n) (ht : t.val < learnLen n E) :
    dlaX I rule E σ t = 0 := by
  apply le_antisymm _ (dlaX_nonneg I rule E σ t)
  exact (dlaX_le_proposal I rule E σ t).trans_eq
    (dlaProposal_eq_zero_of_lt_learnLen I rule E σ t ht)

private theorem firstTimes_succ_of_lt {τ : ℕ} (hτ : τ < n) :
    firstTimes n (τ + 1) = insert ⟨τ, hτ⟩ (firstTimes n τ) := by
  classical
  ext t
  simp only [firstTimes, mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

private theorem firstTimes_eq_univ_of_le {τ : ℕ} (hτ : n ≤ τ) :
    firstTimes n τ = univ := by
  ext t
  simp only [firstTimes, mem_filter, mem_univ, true_and, iff_true]
  exact lt_of_lt_of_le t.isLt hτ

/-- The actual recursive resource state equals the load of all executed prefix decisions,
including at and after the horizon. -/
theorem dlaUsed_eq_sum_firstTimes (τ : ℕ) (i : Fin m) :
    dlaUsed I rule E σ τ i =
      ∑ t ∈ firstTimes n τ, I.arrA σ t i * dlaX I rule E σ t := by
  classical
  induction τ with
  | zero => simp [dlaUsed, firstTimes]
  | succ τ ih =>
      by_cases hτ : τ < n
      · have hnot : (⟨τ, hτ⟩ : Fin n) ∉ firstTimes n τ := by
          simp only [firstTimes, mem_filter, mem_univ, true_and, lt_self_iff_false,
            not_false_eq_true]
        rw [dlaUsed]
        dsimp only
        rw [dif_pos hτ, firstTimes_succ_of_lt hτ, sum_insert hnot, ih]
        change (∑ t ∈ firstTimes n τ, I.arrA σ t i * dlaX I rule E σ t) +
            I.arrA σ ⟨τ, hτ⟩ i * dlaX I rule E σ ⟨τ, hτ⟩ = _
        exact add_comm _ _
      · have hτn : n ≤ τ := Nat.le_of_not_gt hτ
        rw [dlaUsed]
        dsimp only
        rw [dif_neg hτ, firstTimes_eq_univ_of_le (by omega : n ≤ τ + 1)]
        simpa only [firstTimes_eq_univ_of_le hτn] using ih

theorem dlaUsed_nonneg (τ : ℕ) (i : Fin m) : 0 ≤ dlaUsed I rule E σ τ i := by
  rw [dlaUsed_eq_sum_firstTimes]
  exact sum_nonneg fun t _ ↦ mul_nonneg (I.a_nonneg (σ t) i)
    (dlaX_nonneg I rule E σ t)

/-- Executed prefix load is dominated by the corresponding proposal prefix load. -/
theorem dlaUsed_le_proposal_prefix (τ : ℕ) (i : Fin m) :
    dlaUsed I rule E σ τ i ≤
      ∑ t ∈ firstTimes n τ, I.arrA σ t i * dlaProposal I rule E σ t := by
  rw [dlaUsed_eq_sum_firstTimes]
  exact sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left
    (dlaX_le_proposal I rule E σ t) (I.a_nonneg (σ t) i)

theorem dlaUsed_le_total_proposal (τ : ℕ) (i : Fin m) :
    dlaUsed I rule E σ τ i ≤ ∑ t : Fin n, I.arrA σ t i * dlaProposal I rule E σ t := by
  apply (dlaUsed_le_proposal_prefix I rule E σ τ i).trans
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun t _ _ ↦
    mul_nonneg (I.a_nonneg (σ t) i) (dlaProposal_nonneg I rule E σ t)

/-- Before processing a column, used resources plus its full proposal fit below the total
proposal load. This bounds the exact residual-budget guard without assuming prior acceptance. -/
theorem dlaUsed_add_proposal_le_total (t : Fin n) (i : Fin m) :
    dlaUsed I rule E σ t.val i + I.arrA σ t i * dlaProposal I rule E σ t ≤
      ∑ k : Fin n, I.arrA σ k i * dlaProposal I rule E σ k := by
  classical
  have hnot : t ∉ firstTimes n t.val := by
    simp only [firstTimes, mem_filter, mem_univ, true_and, lt_self_iff_false,
      not_false_eq_true]
  calc
    _ ≤ (∑ k ∈ firstTimes n t.val, I.arrA σ k i * dlaProposal I rule E σ k) +
        I.arrA σ t i * dlaProposal I rule E σ t :=
      add_le_add (dlaUsed_le_proposal_prefix I rule E σ t.val i) le_rfl
    _ = ∑ k ∈ insert t (firstTimes n t.val),
        I.arrA σ k i * dlaProposal I rule E σ k := by
      rw [sum_insert hnot, add_comm]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ ↦
      mul_nonneg (I.a_nonneg (σ k) i) (dlaProposal_nonneg I rule E σ k)

/-- Global proposal feasibility makes every actual DLA guard accept. The premise concerns
the proposals, and is supplied by the main theorem's simultaneous phase event. -/
theorem dlaX_eq_proposal_of_total_load_le
    (hload : ∀ i : Fin m,
      (∑ t : Fin n, I.arrA σ t i * dlaProposal I rule E σ t) ≤ I.b i)
    (t : Fin n) : dlaX I rule E σ t = dlaProposal I rule E σ t := by
  classical
  have hguard : ∀ i : Fin m, I.arrA σ t i * dlaProposal I rule E σ t ≤
      I.b i - dlaUsed I rule E σ t.val i := by
    intro i
    have hprefix := dlaUsed_add_proposal_le_total I rule E σ t i
    linarith only [hprefix, hload i]
  simp only [dlaX, dlaDecision, if_pos hguard]

theorem dlaValue_nonneg : 0 ≤ dlaValue I rule E σ := by
  unfold dlaValue
  exact sum_nonneg fun t _ ↦ mul_nonneg (I.π_nonneg (σ t)) (dlaX_nonneg I rule E σ t)

theorem dlaValue_eq_sum_proposal_of_total_load_le
    (hload : ∀ i : Fin m,
      (∑ t : Fin n, I.arrA σ t i * dlaProposal I rule E σ t) ≤ I.b i) :
    dlaValue I rule E σ = ∑ t : Fin n, I.arrPi σ t * dlaProposal I rule E σ t := by
  unfold dlaValue
  exact sum_congr rfl fun t _ ↦ congrArg (fun x : ℝ ↦ I.arrPi σ t * x)
    (dlaX_eq_proposal_of_total_load_le I rule E σ hload t)

end TCSShortlistDLAMain.DLAExecution

/-! Deterministic packing-LP support for the canonical learned-price rule.
The compactness and duality arguments are copied from the accepted local proofs;
resource complementary slackness and the training bounds are proved here.
-/

open scoped BigOperators
open Matrix

namespace DynamicOnlineLP.DLA.DLAMainTrainingPrices

theorem feasibleOptimumExists {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i) :
    ∃ x : α → ℝ, IsPrimalOptimal S π a d x ∧ (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
      (∀ j, j ∉ S → x j = 0) ∧ primalObj S π x = optValue S π a d := by
  classical
  let K : Set (α → ℝ) := {x | IsFeasible S a d x} ∩ Set.Icc 0 1
  have hclosed : IsClosed {x : α → ℝ | IsFeasible S a d x} := by
    have heq : {x : α → ℝ | IsFeasible S a d x} =
        (⋂ i : Fin m, {x : α → ℝ | ∑ t ∈ S, a t i * x t ≤ d i}) ∩
        (⋂ j : α, ⋂ _ : j ∈ S, {x : α → ℝ | 0 ≤ x j ∧ x j ≤ 1}) := by
      ext x
      simp [IsFeasible]
    rw [heq]
    apply IsClosed.inter
    · exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
    · exact isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
        (isClosed_le continuous_const (continuous_apply j)).inter
          (isClosed_le (continuous_apply j) continuous_const)
  have hcompact : IsCompact K := isCompact_Icc.inter_left hclosed
  have hzero : (0 : α → ℝ) ∈ K := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      simpa using hd i
    · simp
    · exact ⟨le_rfl, by intro j; norm_num⟩
  obtain ⟨x, hx, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩
    (show ContinuousOn (primalObj S π) K by unfold primalObj; fun_prop)
  let z : α → ℝ := fun j ↦ if j ∈ S then x j else 0
  have hzfeas : IsFeasible S a d z := by
    constructor
    · simpa [z] using hx.1.1
    · intro j hj
      simpa [z, hj] using hx.1.2 j hj
  have hzbox : ∀ j, 0 ≤ z j ∧ z j ≤ 1 := by
    intro j
    by_cases hj : j ∈ S
    · simpa [z, hj] using And.intro (hx.2.1 j) (hx.2.2 j)
    · simp [z, hj]
  have hobj : primalObj S π z = primalObj S π x := by simp [primalObj, z]
  have hbound (w : α → ℝ) (hw : IsFeasible S a d w) :
      primalObj S π w ≤ primalObj S π z := by
    let w' : α → ℝ := fun j ↦ if j ∈ S then w j else 0
    have hw' : w' ∈ K := by
      refine ⟨?_, ?_⟩
      · constructor
        · simpa [w'] using hw.1
        · intro j hj
          simpa [w', hj] using hw.2 j hj
      · constructor <;> intro j <;> by_cases hj : j ∈ S
        · simpa [w', hj] using (hw.2 j hj).1
        · simp [w', hj]
        · simpa [w', hj] using (hw.2 j hj).2
        · simp [w', hj]
    rw [hobj]
    simpa [primalObj, w'] using hmax hw'
  refine ⟨z, ⟨hzfeas, hbound⟩, hzbox, ?_, ?_⟩
  · intro j hj
    simp [z, hj]
  · have hbd : BddAbove (primalObj S π '' {x | IsFeasible S a d x}) := by
      refine ⟨primalObj S π z, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact hbound w hw
    apply le_antisymm
    · exact le_csSup hbd ⟨z, hzfeas, rfl⟩
    · apply csSup_le
      · exact ⟨primalObj S π z, z, hzfeas, rfl⟩
      · rintro y ⟨w, hw, rfl⟩
        exact hbound w hw

private theorem packing_weak_duality {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsFeasible S a d x) (hy : IsDualFeasible S π a p y) :
    primalObj S π x ≤ dualObj S d p y := by
  classical
  calc
    primalObj S π x ≤ ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
    _ = (∑ i, p i * (∑ t ∈ S, a t i * x t)) + ∑ t ∈ S, y t * x t := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ (∑ i, p i * d i) + ∑ t ∈ S, y t := by
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
      · exact Finset.sum_le_sum fun t ht ↦
          (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
    _ = dualObj S d p y := by simp only [dualObj, mul_comm]

private theorem packing_optimal_values_eq {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsPrimalOptimal S π a d x)
    (hy : IsDualOptimal S π a d p y) : primalObj S π x = dualObj S d p y := by
  classical
  let Row := Fin m ⊕ (↥S ⊕ ↥S)
  let A : Matrix Row ↥S ℝ := fun r t ↦ match r with
    | Sum.inl i => a t i
    | Sum.inr (Sum.inl s) => if s = t then 1 else 0
    | Sum.inr (Sum.inr s) => if s = t then -1 else 0
  let b : Row → ℝ
    | Sum.inl i => d i
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 0
  let c : ↥S → ℝ := fun t ↦ π t
  let dual0 : Row → ℝ
    | Sum.inl i => p i
    | Sum.inr (Sum.inl t) => y t
    | Sum.inr (Sum.inr t) => (∑ i, a t i * p i) + y t - π t
  have hP : ∃ u : ↥S → ℝ, A *ᵥ u ≤ b := by
    refine ⟨fun t ↦ x t, ?_⟩
    rintro (i | t | t)
    · change (∑ t : ↥S, a t.val i * x t.val) ≤ d i
      rw [Finset.sum_coe_sort S (fun t ↦ a t i * x t)]
      exact hx.1.1 i
    · simpa [A, b, Matrix.mulVec, dotProduct] using (hx.1.2 t.val t.property).2
    · simpa [A, b, Matrix.mulVec, dotProduct] using
        neg_nonpos.mpr (hx.1.2 t.val t.property).1
  have hD : ∃ v : Row → ℝ, 0 ≤ v ∧ Aᵀ *ᵥ v = c := by
    refine ⟨dual0, ?_, ?_⟩
    · rintro (i | t | t)
      · exact hy.1.1 i
      · exact (hy.1.2 t.val t.property).1
      · exact sub_nonneg.mpr (hy.1.2 t.val t.property).2
    · funext t
      change (∑ r : Row, A r t * dual0 r) = π t
      simp [Row, A, dual0, Fintype.sum_sum_type]
      ring
  obtain ⟨u, v, hu, hv, hvA, heq, _⟩ := LP.strong_duality_matrix A b c hP hD
  let u' : ι → ℝ := fun t ↦ if ht : t ∈ S then u ⟨t, ht⟩ else 0
  let p' : Fin m → ℝ := fun i ↦ v (Sum.inl i)
  let y' : ι → ℝ := fun t ↦ if ht : t ∈ S then v (Sum.inr (Sum.inl ⟨t, ht⟩)) else 0
  have hu' : IsFeasible S a d u' := by
    constructor
    · intro i
      have h := hu (Sum.inl i)
      change (∑ t : ↥S, a t i * u t) ≤ d i at h
      rw [← Finset.sum_coe_sort S (fun t ↦ a t i * u' t)]
      simpa [u'] using h
    · intro t ht
      have hlo := hu (Sum.inr (Sum.inr ⟨t, ht⟩))
      have hhi := hu (Sum.inr (Sum.inl ⟨t, ht⟩))
      constructor
      · have hlo' : -u ⟨t, ht⟩ ≤ 0 := by
          simpa [Matrix.mulVec, dotProduct, A, b] using hlo
        simpa [u', ht] using neg_nonpos.mp hlo'
      · simpa [Matrix.mulVec, dotProduct, A, b, u', ht] using hhi
  have hy' : IsDualFeasible S π a p' y' := by
    refine ⟨fun i ↦ hv (Sum.inl i), ?_⟩
    intro t ht
    refine ⟨by simpa [y', ht] using hv (Sum.inr (Sum.inl ⟨t, ht⟩)), ?_⟩
    have h := congrFun hvA ⟨t, ht⟩
    have hlo := hv (Sum.inr (Sum.inr ⟨t, ht⟩))
    change (0 : ℝ) ≤ v (Sum.inr (Sum.inr ⟨t, ht⟩)) at hlo
    change (∑ r : Row, A r ⟨t, ht⟩ * v r) = π t at h
    simp [Row, A, Fintype.sum_sum_type] at h
    dsimp [p']
    simp only [y', dif_pos ht]
    linarith
  have hprimal : primalObj S π u' = c ⬝ᵥ u := by
    unfold primalObj
    rw [← Finset.sum_coe_sort S (fun t ↦ π t * u' t)]
    simp [dotProduct, c, u']
  have hdual : dualObj S d p' y' = b ⬝ᵥ v := by
    unfold dualObj
    rw [← Finset.sum_coe_sort S y']
    simp [Row, dotProduct, b, p', y', Fintype.sum_sum_type]
  apply le_antisymm
  · exact packing_weak_duality S π a d x p y hx.1 hy.1
  · calc
      dualObj S d p y ≤ dualObj S d p' y' := hy.2 p' y' hy'
      _ = b ⬝ᵥ v := hdual
      _ = c ⬝ᵥ u := heq.symm
      _ = primalObj S π u' := hprimal.symm
      _ ≤ primalObj S π x := hx.2 u' hu'

private theorem packing_complementarity {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsFeasible S a d x)
    (hy : IsDualFeasible S π a p y) (heq : primalObj S π x = dualObj S d p y) :
    ∀ t ∈ S, ((∑ i, a t i * p i) + y t - π t) * x t = 0 ∧ y t * (1 - x t) = 0 := by
  classical
  let W := ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t
  let R := ∑ i, p i * (∑ t ∈ S, a t i * x t)
  let B := ∑ i, d i * p i
  let Y := ∑ t ∈ S, y t * x t
  let Q := ∑ t ∈ S, y t
  have hW : W = R + Y := by
    dsimp [W, R, Y]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hR : R ≤ B := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
  have hY : Y ≤ Q := Finset.sum_le_sum fun t ht ↦
    (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
  have hfirst : primalObj S π x ≤ W := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
  have hWupper : W ≤ B + Y := by rw [hW]; exact add_le_add hR le_rfl
  have hdual : dualObj S d p y = B + Q := rfl
  have heqW : W = dualObj S d p y := by
    apply le_antisymm
    · exact hWupper.trans (add_le_add le_rfl hY)
    · rw [← heq]
      exact hfirst
  have hYeq : Y = Q := by linarith [heqW, hdual, hWupper]
  have hA0 : (∑ t ∈ S, ((∑ i, a t i * p i) + y t - π t) * x t) = 0 := by
    calc
      _ = W - primalObj S π x := by
        dsimp [W, primalObj]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [heqW, heq]; ring
  have hB0 : (∑ t ∈ S, y t * (1 - x t)) = 0 := by
    calc
      _ = Q - Y := by
        dsimp [Q, Y]
        simp_rw [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hYeq]; ring
  have hApos (t : ι) (ht : t ∈ S) :
      0 ≤ ((∑ i, a t i * p i) + y t - π t) * x t :=
    mul_nonneg (sub_nonneg.mpr (hy.2 t ht).2) (hx.2 t ht).1
  have hBpos (t : ι) (ht : t ∈ S) : 0 ≤ y t * (1 - x t) :=
    mul_nonneg (hy.2 t ht).1 (sub_nonneg.mpr (hx.2 t ht).2)
  intro t ht
  constructor
  · exact le_antisymm ((Finset.single_le_sum hApos ht).trans_eq hA0) (hApos t ht)
  · exact le_antisymm ((Finset.single_le_sum hBpos ht).trans_eq hB0) (hBpos t ht)

theorem thresholdComparison {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsPrimalOptimal S π a d x) (hpy : IsDualOptimal S π a d p y) :
    (∀ t ∈ S, threshold π a p t ≤ x t) ∧
      (GeneralPositionOn S π a → (S.filter (fun t => threshold π a p t ≠ x t)).card ≤ m) := by
  classical
  have heq := packing_optimal_values_eq S π a d x p y hx hpy
  have hcomp := packing_complementarity S π a d x p y hx.1 hpy.1 heq
  have hsum (t : ι) : (∑ i, p i * a t i) = ∑ i, a t i * p i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hthreshold : ∀ t ∈ S, threshold π a p t ≤ x t := by
    intro t ht
    by_cases hπ : π t ≤ ∑ i, p i * a t i
    · simpa [threshold, hπ] using (hx.1.2 t ht).1
    · have hπ' : (∑ i, a t i * p i) < π t := by
        simpa only [hsum t] using lt_of_not_ge hπ
      have hypos : 0 < y t := by linarith [(hpy.1.2 t ht).2]
      have hxone : x t = 1 := by
        rcases mul_eq_zero.mp (hcomp t ht).2 with h | h
        · exact False.elim ((ne_of_gt hypos) h)
        · linarith
      simp [threshold, hπ, hxone]
  refine ⟨hthreshold, ?_⟩
  intro hgp
  apply le_trans (Finset.card_le_card ?_) (hgp p)
  intro t ht
  obtain ⟨htS, hne⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htS, ?_⟩
  by_contra hnot
  rcases lt_or_gt_of_ne hnot with hlt | hgt
  · have hπ : ¬ π t ≤ ∑ i, p i * a t i := not_le_of_gt hlt
    have hxone : x t = 1 := le_antisymm (hx.1.2 t htS).2
      (by simpa [threshold, hπ] using hthreshold t htS)
    exact hne (by simp [threshold, hπ, hxone])
  · have hπ : π t ≤ ∑ i, p i * a t i := le_of_lt hgt
    have hδpos : 0 < (∑ i, a t i * p i) + y t - π t := by
      rw [hsum t] at hgt
      linarith [(hpy.1.2 t htS).1]
    have hxzero : x t = 0 :=
      (mul_eq_zero.mp (hcomp t htS).1).resolve_left (ne_of_gt hδpos)
    exact hne (by simp [threshold, hπ, hxzero])

/-- Zero duality gap forces each resource price times its slack to vanish. -/
theorem resourceComplementarity {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsFeasible S a d x)
    (hy : IsDualFeasible S π a p y) (heq : primalObj S π x = dualObj S d p y) :
    ∀ i, p i * (d i - ∑ t ∈ S, a t i * x t) = 0 := by
  classical
  let W := ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t
  let R := ∑ i, p i * (∑ t ∈ S, a t i * x t)
  let B := ∑ i, d i * p i
  let Y := ∑ t ∈ S, y t * x t
  let Q := ∑ t ∈ S, y t
  have hW : W = R + Y := by
    dsimp [W, R, Y]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hR : R ≤ B := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
  have hY : Y ≤ Q := Finset.sum_le_sum fun t ht ↦
    (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
  have hfirst : primalObj S π x ≤ W := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
  have hdual : dualObj S d p y = B + Q := rfl
  have hReq : R = B := by linarith only [hW, hR, hY, hfirst, heq, hdual]
  have hsum : (∑ i, p i * (d i - ∑ t ∈ S, a t i * x t)) = 0 := by
    calc
      _ = B - R := by
        dsimp [B, R]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hReq]; ring
  have hnonneg (i : Fin m) (_ : i ∈ Finset.univ) :
      0 ≤ p i * (d i - ∑ t ∈ S, a t i * x t) :=
    mul_nonneg (hy.1 i) (sub_nonneg.mpr (hx.1 i))
  intro i
  exact le_antisymm ((Finset.single_le_sum hnonneg (Finset.mem_univ i)).trans_eq hsum)
    (hnonneg i (Finset.mem_univ i))

/-- Every positive-price resource is saturated at a primal optimum. -/
theorem positivePrice_saturated {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsPrimalOptimal S π a d x)
    (hy : IsDualOptimal S π a d p y) (i : Fin m) (hi : 0 < p i) :
    (∑ t ∈ S, a t i * x t) = d i := by
  have h := resourceComplementarity S π a d x p y hx.1 hy.1
    (packing_optimal_values_eq S π a d x p y hx hy) i
  have hzero := (mul_eq_zero.mp h).resolve_left (ne_of_gt hi)
  linarith only [hzero]

/-- Canonical threshold proposals from an optimal dual price are resource feasible. -/
theorem thresholdLoad_le {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ t ∈ S, ∀ i, 0 ≤ a t i) (hp : IsOptimalDualPrice S π a d p) (i : Fin m) :
    (∑ t ∈ S, a t i * threshold π a p t) ≤ d i := by
  obtain ⟨x, hx, _, _, _⟩ := feasibleOptimumExists S π a d hd
  obtain ⟨y, hy⟩ := hp
  have hcomp := (thresholdComparison S π a d x p y hx hy).1
  exact (Finset.sum_le_sum fun t ht ↦
    mul_le_mul_of_nonneg_left (hcomp t ht) (ha t ht i)).trans (hx.1.1 i)

/-- In general position, a positive-price resource loses at most `m` units
when a primal optimum is replaced by its canonical threshold proposal. -/
theorem thresholdLoad_lower {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ t ∈ S, ∀ i, 0 ≤ a t i ∧ a t i ≤ 1)
    (hp : IsOptimalDualPrice S π a d p) (hgp : GeneralPositionOn S π a)
    (i : Fin m) (hi : 0 < p i) :
    d i - (m : ℝ) ≤ ∑ t ∈ S, a t i * threshold π a p t := by
  classical
  obtain ⟨x, hx, _, _, _⟩ := feasibleOptimumExists S π a d hd
  obtain ⟨y, hy⟩ := hp
  have hsat := positivePrice_saturated S π a d x p y hx hy i hi
  have hcard := (thresholdComparison S π a d x p y hx hy).2 hgp
  have hterm (t : α) (ht : t ∈ S) :
      a t i * x t ≤ a t i * threshold π a p t +
        if threshold π a p t ≠ x t then 1 else 0 := by
    by_cases hne : threshold π a p t ≠ x t
    · have hxone : a t i * x t ≤ 1 := by
        calc
          _ ≤ a t i * 1 := mul_le_mul_of_nonneg_left (hx.1.2 t ht).2 (ha t ht i).1
          _ = a t i := mul_one _
          _ ≤ 1 := (ha t ht i).2
      have hthreshold : 0 ≤ threshold π a p t := by
        unfold threshold
        split_ifs <;> norm_num
      have hnonneg := mul_nonneg (ha t ht i).1 hthreshold
      simp only [if_pos hne]
      linarith only [hxone, hnonneg]
    · have heq : threshold π a p t = x t := not_ne_iff.mp hne
      simp only [heq, ne_eq, not_true_eq_false, if_false, add_zero, le_refl]
  have hsum := Finset.sum_le_sum hterm
  have hcount : (∑ t ∈ S, if threshold π a p t ≠ x t then (1 : ℝ) else 0) =
      ((S.filter (fun t ↦ threshold π a p t ≠ x t)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_add_distrib, hcount] at hsum
  have hcard' : ((S.filter (fun t ↦ threshold π a p t ≠ x t)).card : ℝ) ≤ m := by
    exact_mod_cast hcard
  linarith only [hsat, hsum, hcard']

/-- The two deterministic training bounds at an arbitrary canonical optimal dual price. -/
theorem trainingBounds {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i)
    (ha : ∀ t ∈ S, ∀ i, 0 ≤ a t i ∧ a t i ≤ 1)
    (hp : IsOptimalDualPrice S π a d p) (hgp : GeneralPositionOn S π a) :
    ∀ i, (∑ t ∈ S, a t i * threshold π a p t) ≤ d i ∧
      (0 < p i → d i - (m : ℝ) ≤ ∑ t ∈ S, a t i * threshold π a p t) := by
  intro i
  exact ⟨thresholdLoad_le S π a d p hd (fun t ht i ↦ (ha t ht i).1) hp i,
    thresholdLoad_lower S π a d p hd ha hp hgp i⟩

/-- Positive-price resource coverage converts directly into a scaled optimum
bound for canonical threshold revenue. No dual optimality is assumed here. -/
theorem scaledOptimum_le_thresholdRevenue {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (p : Fin m → ℝ) (ρ : ℝ) (hd : ∀ i, 0 ≤ d i) (hp : ∀ i, 0 ≤ p i)
    (hρ : 0 ≤ ρ ∧ ρ ≤ 1)
    (hcoverage : ∀ i, 0 < p i → ρ * d i ≤ ∑ t ∈ S, a t i * threshold π a p t) :
    ρ * optValue S π a d ≤ primalObj S π (threshold π a p) := by
  classical
  let y : α → ℝ := fun t ↦ max (π t - ∑ i, a t i * p i) 0
  have hy0 (t : α) : 0 ≤ y t := le_max_right _ _
  have hy : IsDualFeasible S π a p y := by
    refine ⟨hp, ?_⟩
    intro t ht
    refine ⟨hy0 t, ?_⟩
    have h : π t - ∑ i, a t i * p i ≤ y t := le_max_left _ _
    linarith only [h]
  obtain ⟨x, hx, _, _, hxeq⟩ := feasibleOptimumExists S π a d hd
  have hopt : optValue S π a d ≤ dualObj S d p y := by
    rw [← hxeq]
    exact packing_weak_duality S π a d x p y hx.1 hy
  have hcost (t : α) : (∑ i, p i * a t i) = ∑ i, a t i * p i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcolumn (t : α) : π t * threshold π a p t =
      (∑ i, a t i * p i) * threshold π a p t + y t := by
    by_cases hπ : π t ≤ ∑ i, p i * a t i
    · have hdiff : π t - ∑ i, a t i * p i ≤ 0 := by
        rw [hcost t] at hπ
        exact sub_nonpos.mpr hπ
      simp only [threshold, if_pos hπ, mul_zero, zero_add, y, max_eq_right hdiff]
    · have hdiff : 0 ≤ π t - ∑ i, a t i * p i := by
        rw [hcost t] at hπ
        exact sub_nonneg.mpr (le_of_lt (lt_of_not_ge hπ))
      simp only [threshold, if_neg hπ, mul_one, y, max_eq_left hdiff]
      ring
  have hobj : primalObj S π (threshold π a p) =
      (∑ i, p i * (∑ t ∈ S, a t i * threshold π a p t)) + ∑ t ∈ S, y t := by
    unfold primalObj
    simp_rw [hcolumn, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hprice (i : Fin m) : ρ * (d i * p i) ≤
      p i * (∑ t ∈ S, a t i * threshold π a p t) := by
    by_cases hi : p i = 0
    · simp only [hi, mul_zero, mul_zero, zero_mul, le_refl]
    · have hipos : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hi)
      calc
        ρ * (d i * p i) = p i * (ρ * d i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcoverage i hipos) (hp i)
  have hY : ρ * (∑ t ∈ S, y t) ≤ ∑ t ∈ S, y t := by
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun t ht ↦ hy0 t) hρ.2
  calc
    ρ * optValue S π a d ≤ ρ * dualObj S d p y :=
      mul_le_mul_of_nonneg_left hopt hρ.1
    _ = (∑ i, ρ * (d i * p i)) + ρ * (∑ t ∈ S, y t) := by
      simp only [dualObj, mul_add, Finset.mul_sum]
    _ ≤ (∑ i, p i * (∑ t ∈ S, a t i * threshold π a p t)) + ∑ t ∈ S, y t :=
      add_le_add (Finset.sum_le_sum fun i hi ↦ hprice i) hY
    _ = primalObj S π (threshold π a p) := hobj.symm

end DynamicOnlineLP.DLA.DLAMainTrainingPrices

/-!
Deterministic interfaces for the exact canonical learned-price output. General
position is transported through the actual arrival permutation, and no selected
representative price replaces the dual rule's output.
-/

open scoped BigOperators
open DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.LearnedPrices

/-- General position survives permutation and restriction to any time set. -/
theorem generalPositionOn_arrivals {m n : ℕ} (I : Instance m n)
    (hgp : I.GeneralPosition) (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    GeneralPositionOn S (I.arrPi σ) (I.arrA σ) := by
  classical
  intro p
  have himage :
      (S.filter (fun t => ∑ i : Fin m, p i * I.arrA σ t i = I.arrPi σ t)).image σ ⊆
        Finset.univ.filter (fun j => ∑ i : Fin m, p i * I.a j i = I.π j) := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩
  calc
    (S.filter (fun t => ∑ i : Fin m, p i * I.arrA σ t i = I.arrPi σ t)).card =
        ((S.filter (fun t => ∑ i : Fin m, p i * I.arrA σ t i = I.arrPi σ t)).image σ).card :=
      (Finset.card_image_of_injective _ σ.injective).symm
    _ ≤ (Finset.univ.filter (fun j => ∑ i : Fin m, p i * I.a j i = I.π j)).card :=
      Finset.card_le_card himage
    _ ≤ m := hgp p

/-- The canonical learned price is optimal for its exact training right side. -/
theorem learnedPrice_optimal {m n : ℕ} (I : Instance m n) (rule : DualRule m n)
    (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hvalid : IsValidDualRule rule)
    (hℓ : ℓ ≤ n)
    (hd : ∀ i, 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i) :
    IsOptimalDualPrice (firstTimes n ℓ) (I.arrPi σ) (I.arrA σ)
      (fun i => (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
      (learnedPrice I rule E σ ℓ) := by
  exact hvalid.2 ℓ (I.arrPi σ) (I.arrA σ) _ hℓ hd

/-- Validity forces every coordinate of the actual learned price to be nonnegative. -/
theorem learnedPrice_nonneg {m n : ℕ} (I : Instance m n) (rule : DualRule m n)
    (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hvalid : IsValidDualRule rule)
    (hℓ : ℓ ≤ n)
    (hd : ∀ i, 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i) :
    ∀ i, 0 ≤ learnedPrice I rule E σ ℓ i := by
  obtain ⟨y, hy⟩ := learnedPrice_optimal I rule E σ ℓ hvalid hℓ hd
  exact hy.1.1

/-- Both training bounds hold for the output of the canonical dual rule itself. -/
theorem learnedPrice_trainingBounds {m n : ℕ} (I : Instance m n) (rule : DualRule m n)
    (E : ℕ) (σ : Equiv.Perm (Fin n)) (ℓ : ℕ) (hvalid : IsValidDualRule rule)
    (hℓ : ℓ ≤ n)
    (hd : ∀ i, 0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
    (hgp : I.GeneralPosition) :
    ∀ i,
      (∑ t ∈ firstTimes n ℓ,
        I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ)
          (learnedPrice I rule E σ ℓ) t) ≤
          (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i ∧
      (0 < learnedPrice I rule E σ ℓ i →
        (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i - (m : ℝ) ≤
          ∑ t ∈ firstTimes n ℓ,
            I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ)
              (learnedPrice I rule E σ ℓ) t) := by
  exact DLAMainTrainingPrices.trainingBounds (firstTimes n ℓ) (I.arrPi σ) (I.arrA σ)
    (fun i => (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
    (learnedPrice I rule E σ ℓ) hd
    (fun t _ i => ⟨I.a_nonneg (σ t) i, I.a_le_one (σ t) i⟩)
    (learnedPrice_optimal I rule E σ ℓ hvalid hℓ hd)
    (generalPositionOn_arrivals I hgp σ (firstTimes n ℓ))

/-- A fixed Boolean pattern defines a population in the interval `[0,1]`. -/
theorem pattern_population_bounds {m n : ℕ} (I : Instance m n)
    (v : Fin n → Bool) (i : Fin m) :
    ∀ j, 0 ≤ (if v j then I.a j i else 0) ∧ (if v j then I.a j i else 0) ≤ 1 := by
  intro j
  split_ifs
  · exact ⟨I.a_nonneg j i, I.a_le_one j i⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- The strict base-column pattern is the exact threshold load after permutation. -/
theorem threshold_population_eq {m n : ℕ} (I : Instance m n)
    (σ : Equiv.Perm (Fin n)) (p : Fin m → ℝ) (i : Fin m) (t : Fin n) :
    (if decide ((∑ k : Fin m, p k * I.a (σ t) k) < I.π (σ t))
      then I.a (σ t) i else 0) =
        I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ) p t := by
  classical
  by_cases h : I.π (σ t) ≤ ∑ k : Fin m, p k * I.a (σ t) k
  · simp [threshold, Instance.arrPi, Instance.arrA, h, not_lt.mpr h]
  · simp [threshold, Instance.arrPi, Instance.arrA, h, lt_of_not_ge h]

/-- The population identity also holds on every fixed time set. -/
theorem threshold_population_sum_eq {m n : ℕ} (I : Instance m n)
    (σ : Equiv.Perm (Fin n)) (p : Fin m → ℝ) (i : Fin m) (S : Finset (Fin n)) :
    (∑ t ∈ S, if decide ((∑ k : Fin m, p k * I.a (σ t) k) < I.π (σ t))
      then I.a (σ t) i else 0) =
        ∑ t ∈ S, I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ) p t := by
  apply Finset.sum_congr rfl
  intro t _
  exact threshold_population_eq I σ p i t

/-- Difference of the two prefix sets is the exact window in Lemma 5. -/
theorem secondBlock_eq_window (n ℓ : ℕ) :
    (firstTimes n (2 * ℓ)) \ firstTimes n ℓ =
      Finset.univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ) := by
  ext t
  simp only [Finset.mem_sdiff, firstTimes, Finset.mem_filter, Finset.mem_univ,
    true_and, not_lt]
  exact and_comm

end TCSShortlistDLAMain.LearnedPrices

/-!
Value adapters for the actual canonical partial packing LPs. The full-horizon
identity transports both resource feasibility and objective values through the
arrival permutation; it does not identify optima merely by reindexing revenue.
-/

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.LearnedPrices

/-- A feasible allocation is bounded by the true attained canonical optimum. -/
theorem feasible_primalObj_le_optValue {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (x : α → ℝ) (hd : ∀ i, 0 ≤ d i) (hx : IsFeasible S a d x) :
    primalObj S π x ≤ optValue S π a d := by
  obtain ⟨z, hz, _, _, hzeq⟩ := DLAMainTrainingPrices.feasibleOptimumExists S π a d hd
  rw [← hzeq]
  exact hz.2 x hx

/-- Nonnegative budgets make zero feasible, so the canonical optimum is nonnegative. -/
theorem optValue_nonneg {α : Type} [Fintype α] [DecidableEq α]
    {m : ℕ} (S : Finset α) (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i) : 0 ≤ optValue S π a d := by
  have hz : IsFeasible S a d (fun _ ↦ 0) := by
    constructor
    · intro i
      simpa only [mul_zero, sum_const_zero] using hd i
    · intro t ht
      norm_num
  simpa only [primalObj, mul_zero, sum_const_zero] using
    feasible_primalObj_le_optValue S π a d (fun _ ↦ 0) hd hz

/-- A partial optimum is nonnegative at every nonnegative right side. -/
theorem partialOPT_nonneg {m n : ℕ} (I : Instance m n) (σ : Equiv.Perm (Fin n))
    (s : ℕ) (d : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i) :
    0 ≤ I.partialOPT σ s d :=
  optValue_nonneg (firstTimes n s) (I.arrPi σ) (I.arrA σ) d hd

/-- The proportionally budgeted partial optima used in the loss expansion are nonnegative. -/
theorem scaled_partialOPT_nonneg {m n : ℕ} (I : Instance m n)
    (σ : Equiv.Perm (Fin n)) (s : ℕ) (hb : ∀ i, 0 ≤ I.b i) :
    0 ≤ I.partialOPT σ s (fun i ↦ ((s : ℝ) / n) * I.b i) := by
  apply partialOPT_nonneg
  intro i
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (hb i)

/-- The full canonical optimum is nonnegative when its budgets are nonnegative. -/
theorem OPT_nonneg {m n : ℕ} (I : Instance m n) (hb : ∀ i, 0 ≤ I.b i) : 0 ≤ I.OPT :=
  optValue_nonneg univ I.π I.a I.b hb

/-- Reindexing a full-horizon allocation transports every actual resource constraint
and every box constraint, in both directions. -/
theorem isFeasible_univ_reindex_iff {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (a : α → Fin m → ℝ) (d : Fin m → ℝ) (σ : Equiv.Perm α) (x : α → ℝ) :
    IsFeasible univ (fun t ↦ a (σ t)) d x ↔
      IsFeasible univ a d (fun j ↦ x (σ.symm j)) := by
  have hload (i : Fin m) : (∑ t, a (σ t) i * x t) =
      ∑ j, a j i * x (σ.symm j) := by
    simpa only [σ.symm_apply_apply] using
      (Equiv.sum_comp σ (fun j ↦ a j i * x (σ.symm j)))
  constructor
  · intro hx
    constructor
    · intro i
      rw [← hload i]
      exact hx.1 i
    · intro j hj
      exact hx.2 (σ.symm j) (mem_univ _)
  · intro hx
    constructor
    · intro i
      rw [hload i]
      exact hx.1 i
    · intro t ht
      simpa only [σ.symm_apply_apply] using hx.2 (σ t) (mem_univ _)

/-- Full-horizon objectives are transported by the same allocation reindexing. -/
theorem primalObj_univ_reindex {α : Type} [Fintype α] [DecidableEq α]
    (π : α → ℝ) (σ : Equiv.Perm α) (x : α → ℝ) :
    primalObj univ (fun t ↦ π (σ t)) x =
      primalObj univ π (fun j ↦ x (σ.symm j)) := by
  simpa only [primalObj, σ.symm_apply_apply] using
    (Equiv.sum_comp σ (fun j ↦ π j * x (σ.symm j)))

/-- Full-horizon optima are invariant under permutation because the complete
sets of feasible objective values agree. This holds even without a budget sign premise. -/
theorem optValue_univ_perm {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (π : α → ℝ) (a : α → Fin m → ℝ) (d : Fin m → ℝ) (σ : Equiv.Perm α) :
    optValue univ (fun t ↦ π (σ t)) (fun t ↦ a (σ t)) d = optValue univ π a d := by
  unfold optValue
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun j ↦ x (σ.symm j), (isFeasible_univ_reindex_iff a d σ x).mp hx, ?_⟩
    exact (primalObj_univ_reindex π σ x).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun t ↦ x (σ t), ?_, ?_⟩
    · apply (isFeasible_univ_reindex_iff a d σ (fun t ↦ x (σ t))).mpr
      simpa only [Set.mem_setOf_eq, σ.apply_symm_apply] using hx
    · simpa only [σ.apply_symm_apply] using
        primalObj_univ_reindex π σ (fun t ↦ x (σ t))

/-- The complete time prefix is exactly the full finite horizon. -/
theorem firstTimes_full (n : ℕ) : firstTimes n n = (univ : Finset (Fin n)) := by
  ext t
  simp only [firstTimes, mem_filter, mem_univ, true_and, t.isLt]

/-- The full proportionally budgeted partial optimum is the original canonical
`I.OPT`; both feasibility and revenue are reindexed through the actual permutation. -/
theorem partialOPT_full_horizon {m n : ℕ} (I : Instance m n)
    (σ : Equiv.Perm (Fin n)) (hn : 0 < n) :
    I.partialOPT σ n (fun i ↦ ((n : ℝ) / n) * I.b i) = I.OPT := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Instance.partialOPT Instance.OPT
  rw [firstTimes_full]
  simp only [div_self hnreal, one_mul]
  exact optValue_univ_perm I.π I.a I.b σ

/-- The actual price's training revenue is bounded by the canonical partial
optimum at the unshrunk proportional budget. General position is unnecessary
for this upper bound. -/
theorem learnedPrice_trainingRevenue_le_partialOPT {m n E ℓ : ℕ}
    (I : Instance m n) (rule : DualRule m n) (σ : Equiv.Perm (Fin n))
    (hn : 0 < n) (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n) (hℓ : ℓ ∈ phases n E)
    (hvalid : IsValidDualRule rule) (hb : ∀ i, 0 ≤ I.b i) :
    (∑ t ∈ firstTimes n ℓ, I.arrPi σ t *
      threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t) ≤
        I.partialOPT σ ℓ (fun i ↦ ((ℓ : ℝ) / n) * I.b i) := by
  have htime := phase_time_bounds hn hdvd hℓ
  have hslack := phase_slack_bounds hn hE hdvd hℓ
  have hratio : 0 ≤ (ℓ : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hd (i : Fin m) : 0 ≤ ((ℓ : ℝ) / n) * I.b i := mul_nonneg hratio (hb i)
  have hdtrain (i : Fin m) :
      0 ≤ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hslack.2) hratio) (hb i)
  have hoptimal := learnedPrice_optimal I rule E σ ℓ hvalid (by omega : ℓ ≤ n) hdtrain
  have hfeasible : IsFeasible (firstTimes n ℓ) (I.arrA σ)
      (fun i ↦ ((ℓ : ℝ) / n) * I.b i)
      (threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ)) := by
    constructor
    · intro i
      have hload := DLAMainTrainingPrices.thresholdLoad_le (firstTimes n ℓ)
        (I.arrPi σ) (I.arrA σ)
        (fun i ↦ (1 - slack n E ℓ) * ((ℓ : ℝ) / n) * I.b i)
        (learnedPrice I rule E σ ℓ) hdtrain
        (fun t ht i ↦ I.a_nonneg (σ t) i) hoptimal i
      apply hload.trans
      simpa only [mul_assoc] using
        mul_le_of_le_one_left (hd i) (sub_le_self 1 hslack.1.le)
    · intro t ht
      unfold threshold
      split_ifs <;> norm_num
  exact feasible_primalObj_le_optValue (firstTimes n ℓ) (I.arrPi σ) (I.arrA σ)
    (fun i ↦ ((ℓ : ℝ) / n) * I.b i)
    (threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ)) hd hfeasible

end TCSShortlistDLAMain.LearnedPrices

/-!
Deterministic consequences of the exact pointwise learned-price feasibility and
near-optimality events. The canonical guarded execution is retained throughout.
-/

open Finset DynamicOnlineLP.DLA TCSShortlistDLAMain.DLAExecution

namespace TCSShortlistDLAMain.LearnedPrices

/-- On a canonical phase window, the actual proposal uses exactly that phase's price. -/
theorem dlaProposal_eq_threshold_of_mem_window {m n E ℓ : ℕ}
    (I : Instance m n) (rule : DualRule m n) (σ : Equiv.Perm (Fin n))
    (hn : 0 < n) (hdvd : 2 ^ E ∣ n) (hℓ : ℓ ∈ phases n E)
    (t : Fin n) (ht : ℓ ≤ t.val ∧ t.val < 2 * ℓ) :
    dlaProposal I rule E σ t =
      threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t := by
  have hstart := phaseStart_eq_of_mem_window hn hdvd hℓ ht.1 ht.2
  have hlearn : ¬t.val < learnLen n E :=
    not_lt.mpr ((phase_time_bounds hn hdvd hℓ).2.2.trans ht.1)
  simp only [dlaProposal, if_neg hlearn, hstart]

/-- The exact pointwise feasibility event bounds the full nonnegative proposal load. -/
theorem total_proposal_load_le_budget {m n E : ℕ}
    (I : Instance m n) (rule : DualRule m n) (σ : Equiv.Perm (Fin n))
    (hn : 0 < n) (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n) (hb : ∀ i, 0 ≤ I.b i)
    (hF : ∀ ℓ ∈ phases n E, ∀ i : Fin m,
      (∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
        I.arrA σ t i *
          threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t) ≤
        ((ℓ : ℝ) / (n : ℝ)) * I.b i) (i : Fin m) :
    (∑ t : Fin n, I.arrA σ t i * dlaProposal I rule E σ t) ≤ I.b i := by
  calc
    _ = ∑ ℓ ∈ phases n E,
        ∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
          I.arrA σ t i * dlaProposal I rule E σ t := by
      apply sum_eq_sum_phases n E hn hdvd
      intro t ht
      rw [dlaProposal_eq_zero_of_lt_learnLen I rule E σ t ht, mul_zero]
    _ = ∑ ℓ ∈ phases n E,
        ∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
          I.arrA σ t i *
            threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t := by
      apply sum_congr rfl
      intro ℓ hℓ
      apply sum_congr rfl
      intro t ht
      rw [dlaProposal_eq_threshold_of_mem_window I rule σ hn hdvd hℓ t
        (mem_filter.mp ht).2]
    _ ≤ ∑ ℓ ∈ phases n E, ((ℓ : ℝ) / (n : ℝ)) * I.b i :=
      sum_le_sum fun ℓ hℓ ↦ hF ℓ hℓ i
    _ = (1 - eps E) * I.b i := by
      rw [← sum_mul, (phase_sums n E hn hE hdvd).1]
    _ ≤ I.b i := mul_le_of_le_one_left (hb i) (sub_le_self 1 (eps_pos E).le)

/-- With globally feasible canonical phase proposals, actual executed value decomposes
as the sum of the exact canonical threshold revenues on the phase windows. -/
theorem dlaValue_eq_sum_phase_revenues_of_phase_feasible {m n E : ℕ}
    (I : Instance m n) (rule : DualRule m n) (σ : Equiv.Perm (Fin n))
    (hn : 0 < n) (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n) (hb : ∀ i, 0 ≤ I.b i)
    (hF : ∀ ℓ ∈ phases n E, ∀ i : Fin m,
      (∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
        I.arrA σ t i *
          threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t) ≤
        ((ℓ : ℝ) / (n : ℝ)) * I.b i) :
    dlaValue I rule E σ = ∑ ℓ ∈ phases n E,
      ∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
        I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ)
          (learnedPrice I rule E σ ℓ) t := by
  rw [dlaValue_eq_sum_proposal_of_total_load_le I rule E σ
    (total_proposal_load_le_budget I rule σ hn hE hdvd hb hF)]
  rw [sum_eq_sum_phases n E hn hdvd _ (fun t ht ↦ by
    rw [dlaProposal_eq_zero_of_lt_learnLen I rule E σ t ht, mul_zero])]
  apply sum_congr rfl
  intro ℓ hℓ
  apply sum_congr rfl
  intro t ht
  rw [dlaProposal_eq_threshold_of_mem_window I rule σ hn hdvd hℓ t
    (mem_filter.mp ht).2]

/-- A phase window is exactly its doubled prefix minus its training prefix. -/
theorem sum_window_eq_sub_prefixes {n : ℕ} (f : Fin n → ℝ) (ℓ : ℕ) :
    (∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ), f t) =
      (∑ t ∈ firstTimes n (2 * ℓ), f t) - ∑ t ∈ firstTimes n ℓ, f t := by
  rw [← secondBlock_eq_window]
  apply sum_sdiff_eq_sub
  intro t ht
  simp only [firstTimes, mem_filter, mem_univ, true_and] at *
  omega

/-- The exact pointwise F and N events give the signed loss expansion for actual DLA
value. The canonical near-optimality coefficient is never replaced by a positive part. -/
theorem opt_sub_losses_le_dlaValue_of_phase_events {m n E : ℕ}
    (I : Instance m n) (rule : DualRule m n) (σ : Equiv.Perm (Fin n))
    (hn : 0 < n) (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n)
    (hvalid : IsValidDualRule rule) (hb : ∀ i, 0 ≤ I.b i)
    (hF : ∀ ℓ ∈ phases n E, ∀ i : Fin m,
      (∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
        I.arrA σ t i *
          threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t) ≤
        ((ℓ : ℝ) / (n : ℝ)) * I.b i)
    (hN : ∀ ℓ ∈ phases n E,
      (1 - 2 * slack n E ℓ - eps E) *
          I.partialOPT σ (2 * ℓ) (fun i => (2 * (ℓ : ℝ) / (n : ℝ)) * I.b i) ≤
        ∑ t ∈ firstTimes n (2 * ℓ),
          I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ)
            (learnedPrice I rule E σ ℓ) t) :
    I.OPT - I.partialOPT σ (learnLen n E)
        (fun i => ((learnLen n E : ℝ) / (n : ℝ)) * I.b i) -
      (∑ ℓ ∈ phases n E, (2 * slack n E ℓ + eps E) *
        I.partialOPT σ (2 * ℓ) (fun i => (((2 * ℓ : ℕ) : ℝ) / (n : ℝ)) * I.b i)) ≤
      dlaValue I rule E σ := by
  let V : ℕ → ℝ := fun s ↦ I.partialOPT σ s (fun i ↦ ((s : ℝ) / n) * I.b i)
  have hvalue := dlaValue_eq_sum_phase_revenues_of_phase_feasible
    I rule σ hn hE hdvd hb hF
  have hblock (ℓ : ℕ) (hℓ : ℓ ∈ phases n E) :
      (1 - 2 * slack n E ℓ - eps E) * V (2 * ℓ) - V ℓ ≤
        ∑ t ∈ univ.filter (fun t : Fin n => ℓ ≤ t.val ∧ t.val < 2 * ℓ),
          I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ)
            (learnedPrice I rule E σ ℓ) t := by
    have hnear : (1 - 2 * slack n E ℓ - eps E) * V (2 * ℓ) ≤
        ∑ t ∈ firstTimes n (2 * ℓ),
          I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ)
            (learnedPrice I rule E σ ℓ) t := by
      simpa only [V, Nat.cast_mul, Nat.cast_ofNat] using hN ℓ hℓ
    have htrain : (∑ t ∈ firstTimes n ℓ,
        I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ)
          (learnedPrice I rule E σ ℓ) t) ≤ V ℓ :=
      learnedPrice_trainingRevenue_le_partialOPT I rule σ hn hE hdvd hℓ hvalid hb
    rw [sum_window_eq_sub_prefixes]
    linarith only [hnear, htrain]
  have hsum : (∑ ℓ ∈ phases n E,
      ((1 - 2 * slack n E ℓ - eps E) * V (2 * ℓ) - V ℓ)) ≤ dlaValue I rule E σ := by
    rw [hvalue]
    exact sum_le_sum hblock
  have hexpand : (∑ ℓ ∈ phases n E,
      ((1 - 2 * slack n E ℓ - eps E) * V (2 * ℓ) - V ℓ)) =
      (∑ ℓ ∈ phases n E, (V (2 * ℓ) - V ℓ)) -
        ∑ ℓ ∈ phases n E, (2 * slack n E ℓ + eps E) * V (2 * ℓ) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro ℓ hℓ
    ring
  rw [hexpand, dyadic_telescope n E hn hdvd V] at hsum
  have hfull : V n = I.OPT := partialOPT_full_horizon I σ hn
  rw [hfull] at hsum
  exact hsum

end TCSShortlistDLAMain.LearnedPrices

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.LearnedPrices

private theorem probPerm_eq_count {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    [DecidablePred P] : probPerm P =
      ((univ.filter P).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  unfold probPerm
  congr

theorem probPerm_not {n : ℕ} (P : Equiv.Perm (Fin n) → Prop) :
    probPerm (fun σ ↦ ¬P σ) = 1 - probPerm P := by
  classical
  have hn : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcard : ((univ.filter P).card : ℝ) +
      ((univ.filter (fun σ ↦ ¬P σ)).card : ℝ) =
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast (card_filter_add_card_filter_not (s := univ) P)
  simp only [probPerm_eq_count]
  apply eq_sub_iff_add_eq.mpr
  rw [← add_div]
  apply (div_eq_one_iff_eq hn).mpr
  linarith only [hcard]

theorem probPerm_exists_le_sum {α : Type*} {n : ℕ} (s : Finset α)
    (P : α → Equiv.Perm (Fin n) → Prop) :
    probPerm (fun σ ↦ ∃ i ∈ s, P i σ) ≤ ∑ i ∈ s, probPerm (P i) := by
  classical
  have hset : (univ.filter (fun σ : Equiv.Perm (Fin n) ↦ ∃ i ∈ s, P i σ)) =
      s.biUnion (fun i ↦ univ.filter (P i)) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
  have hcard : (s.biUnion (fun i ↦ univ.filter (P i))).card ≤
      ∑ i ∈ s, (univ.filter (P i)).card := card_biUnion_le
  have hcast : ((s.biUnion (fun i ↦ univ.filter (P i))).card : ℝ) ≤
      ∑ i ∈ s, ((univ.filter (P i)).card : ℝ) := by exact_mod_cast hcard
  simp only [probPerm_eq_count]
  rw [hset]
  calc
    _ ≤ (∑ i ∈ s, ((univ.filter (P i)).card : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
      div_le_div_of_nonneg_right hcast (Nat.cast_nonneg _)
    _ = _ := sum_div _ _ _

theorem probPerm_forall_ge_one_sub_sum {α : Type*} {n : ℕ} (s : Finset α)
    (P : α → Equiv.Perm (Fin n) → Prop) :
    1 - (∑ i ∈ s, probPerm (fun σ ↦ ¬P i σ)) ≤
      probPerm (fun σ ↦ ∀ i ∈ s, P i σ) := by
  classical
  have hbad := probPerm_exists_le_sum s (fun i σ ↦ ¬P i σ)
  have hc := probPerm_not (fun σ ↦ ∀ i ∈ s, P i σ)
  simp only [not_forall, exists_prop] at hc
  linarith

end TCSShortlistDLAMain.LearnedPrices

/-! Finite uniform averages, event indicators, and nonnegative loss accounting
for the canonical DLA expectation. No independence assumptions are used. -/

open Finset DynamicOnlineLP.DLA

namespace TCSShortlistDLAMain.DLAExpectation

private theorem probPerm_count_for_average {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    [DecidablePred P] : probPerm P =
      ((univ.filter P).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  unfold probPerm
  congr

theorem avgPerm_mono {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ)
    (h : ∀ σ, f σ ≤ g σ) : avgPerm f ≤ avgPerm g := by
  unfold avgPerm
  exact div_le_div_of_nonneg_right (sum_le_sum fun σ _ => h σ) (Nat.cast_nonneg _)

theorem avgPerm_const {n : ℕ} (c : ℝ) :
    avgPerm (fun _ : Equiv.Perm (Fin n) => c) = c := by
  have hP : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold avgPerm
  apply (div_eq_iff hP).mpr
  simp only [sum_const, nsmul_eq_mul, card_univ, mul_comm]

theorem avgPerm_add {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ) :
    avgPerm (fun σ => f σ + g σ) = avgPerm f + avgPerm g := by
  simp only [avgPerm, sum_add_distrib, add_div]

theorem avgPerm_sub {n : ℕ} (f g : Equiv.Perm (Fin n) → ℝ) :
    avgPerm (fun σ => f σ - g σ) = avgPerm f - avgPerm g := by
  simp only [avgPerm, sum_sub_distrib, sub_div]

theorem avgPerm_mul_left {n : ℕ} (c : ℝ) (f : Equiv.Perm (Fin n) → ℝ) :
    avgPerm (fun σ => c * f σ) = c * avgPerm f := by
  simp only [avgPerm, ← Finset.mul_sum, mul_div_assoc]

theorem avgPerm_sum {α : Type*} {n : ℕ} (S : Finset α)
    (f : α → Equiv.Perm (Fin n) → ℝ) :
    avgPerm (fun σ => ∑ i ∈ S, f i σ) = ∑ i ∈ S, avgPerm (f i) := by
  unfold avgPerm
  rw [sum_comm, sum_div]

theorem avgPerm_indicator_const {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    [DecidablePred P] (c : ℝ) :
    avgPerm (fun σ => if P σ then c else 0) = probPerm P * c := by
  rw [probPerm_count_for_average]
  unfold avgPerm
  rw [← sum_filter, sum_const, nsmul_eq_mul, div_mul_eq_mul_div]

theorem avgPerm_indicator_le {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    [DecidablePred P] (f : Equiv.Perm (Fin n) → ℝ) (hf : ∀ σ, 0 ≤ f σ) :
    avgPerm (fun σ => if P σ then f σ else 0) ≤ avgPerm f := by
  apply avgPerm_mono
  intro σ
  split_ifs
  · exact le_rfl
  · exact hf σ

/-- A lower bound on a good event loses at most the unconditional mean of a
nonnegative loss. The constant `O` itself may have either sign. -/
theorem good_event_loss_bound {n : ℕ} (f loss : Equiv.Perm (Fin n) → ℝ)
    (O : ℝ) (G : Equiv.Perm (Fin n) → Prop) [DecidablePred G]
    (hf : ∀ σ, 0 ≤ f σ) (hloss : ∀ σ, 0 ≤ loss σ)
    (hgood : ∀ σ, G σ → O - loss σ ≤ f σ) :
    probPerm G * O - avgPerm loss ≤ avgPerm f := by
  have hpoint : ∀ σ,
      (if G σ then O else 0) - (if G σ then loss σ else 0) ≤ f σ := by
    intro σ
    by_cases hG : G σ
    · simpa only [if_pos hG] using hgood σ hG
    · simpa only [if_neg hG, sub_self] using hf σ
  have hbound : avgPerm (fun σ => if G σ then O else 0) -
      avgPerm (fun σ => if G σ then loss σ else 0) ≤ avgPerm f := by
    rw [← avgPerm_sub]
    exact avgPerm_mono _ _ hpoint
  rw [avgPerm_indicator_const] at hbound
  have hdrop := avgPerm_indicator_le G loss hloss
  linarith only [hbound, hdrop]

/-- Finite union control of the two bad events; no independence is assumed. -/
theorem probPerm_and_ge {n : ℕ} (P Q : Equiv.Perm (Fin n) → Prop) :
    probPerm P + probPerm Q - 1 ≤ probPerm (fun σ => P σ ∧ Q σ) := by
  classical
  have h := TCSShortlistDLAMain.LearnedPrices.probPerm_forall_ge_one_sub_sum
    (univ : Finset Bool) (fun b σ => if b then P σ else Q σ)
  have h' : 1 - ((1 - probPerm P) + (1 - probPerm Q)) ≤
      probPerm (fun σ => P σ ∧ Q σ) := by
    simpa only [Fintype.sum_bool, mem_univ, forall_const, Bool.forall_bool,
      Bool.false_eq_true, if_false, if_true,
      TCSShortlistDLAMain.LearnedPrices.probPerm_not, and_comm] using h
  linarith only [h']

end TCSShortlistDLAMain.DLAExpectation

open Finset DynamicOnlineLP.DLA TCSShortlistDLAMain.LearnedPrices TCSShortlistDLAMain.DLAExpectation

namespace TCSShortlistDLAMain.DLAExpectation

theorem expected_partial_losses_le {m n E : ℕ} (I : Instance m n)
    (hb : ∀ i, 0 ≤ I.b i) (hn : 0 < n) (hE : 1 ≤ E) (hdvd : 2 ^ E ∣ n) :
    avgPerm (fun σ : Equiv.Perm (Fin n) ↦
      I.partialOPT σ (learnLen n E) (fun i ↦ ((learnLen n E : ℕ) : ℝ) / n * I.b i) +
        ∑ ℓ ∈ phases n E, (2 * slack n E ℓ + eps E) *
          I.partialOPT σ (2 * ℓ) (fun i ↦ ((2 * ℓ : ℕ) : ℝ) / n * I.b i)) ≤
      13 * eps E * I.OPT := by
  classical
  let V : ℕ → Equiv.Perm (Fin n) → ℝ :=
    fun k σ ↦ I.partialOPT σ k (fun i ↦ (k : ℝ) / n * I.b i)
  let c : ℕ → ℝ := fun ℓ ↦ 2 * slack n E ℓ + eps E
  have hO : 0 ≤ I.OPT := OPT_nonneg I hb
  have heps := TCSShortlistDLAMain.LearnedPrices.eps_pos E
  have hc (ℓ : ℕ) : 0 ≤ c ℓ := by dsimp [c, slack]; positivity
  have hlen : learnLen n E ≤ n := Nat.div_le_self _ _
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hscale : ((learnLen n E : ℕ) : ℝ) / n = eps E := by
    symm
    exact (eq_div_iff hn0).mpr (eps_mul_population_eq_learnLen hdvd)
  have hphase := phase_sums n E hn hE hdvd
  have hS := hphase.1
  have hH : (∑ ℓ ∈ phases n E, slack n E ℓ * ((ℓ : ℝ) / n)) ≤ 2.5 * eps E :=
    hphase.2.1.trans_le hphase.2.2
  have hweights : (∑ ℓ ∈ phases n E, c ℓ * (((2 * ℓ : ℕ) : ℝ) / n)) ≤
      12 * eps E := by
    have heq : (∑ ℓ ∈ phases n E, c ℓ * (((2 * ℓ : ℕ) : ℝ) / n)) =
        4 * (∑ ℓ ∈ phases n E, slack n E ℓ * ((ℓ : ℝ) / n)) +
          2 * eps E * (∑ ℓ ∈ phases n E, (ℓ : ℝ) / n) := by
      calc
        _ = ∑ ℓ ∈ phases n E,
            (4 * (slack n E ℓ * ((ℓ : ℝ) / n)) + 2 * eps E * ((ℓ : ℝ) / n)) := by
          apply sum_congr rfl
          intro ℓ _
          dsimp [c]
          push_cast
          ring
        _ = _ := by simp only [sum_add_distrib, Finset.mul_sum]
    rw [heq, hS]
    nlinarith only [hH, sq_nonneg (eps E)]
  change avgPerm (fun σ ↦ V (learnLen n E) σ +
    ∑ ℓ ∈ phases n E, c ℓ * V (2 * ℓ) σ) ≤ _
  rw [avgPerm_add, avgPerm_sum]
  simp_rw [avgPerm_mul_left]
  calc
    _ ≤ (((learnLen n E : ℕ) : ℝ) / n) * I.OPT +
        ∑ ℓ ∈ phases n E, c ℓ * ((((2 * ℓ : ℕ) : ℝ) / n) * I.OPT) := by
      apply add_le_add (expected_partialOPT_le I hb _ hlen)
      apply sum_le_sum
      intro ℓ hℓ
      exact mul_le_mul_of_nonneg_left
        (expected_partialOPT_le I hb (2 * ℓ) (phase_time_bounds hn hdvd hℓ).2.1) (hc ℓ)
    _ = (eps E + ∑ ℓ ∈ phases n E, c ℓ * (((2 * ℓ : ℕ) : ℝ) / n)) * I.OPT := by
      rw [hscale, add_mul, Finset.sum_mul]
      congr 1
      apply sum_congr rfl
      intro ℓ _
      ring
    _ ≤ (eps E + 12 * eps E) * I.OPT :=
      mul_le_mul_of_nonneg_right (add_le_add le_rfl hweights) hO
    _ = 13 * eps E * I.OPT := by ring

end TCSShortlistDLAMain.DLAExpectation

open Finset DynamicOnlineLP.DLA TCSShortlistDLAMain.LearnedPrices TCSShortlistDLAMain.DLAExpectation

theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (m n E : ℕ) (I : Instance m n) (rule : DualRule m n),
        1 ≤ m → 1 ≤ E → 0 < n → 2 ^ E ∣ n → I.GeneralPosition → IsValidDualRule rule →
        (∀ i : Fin m, C₁ * (m : ℝ) * Real.log ((n : ℝ) / eps E) / eps E ^ 2 ≤ I.b i) →
        (1 - C₂ * eps E) * I.OPT ≤ avgPerm (fun σ : Equiv.Perm (Fin n) => dlaValue I rule E σ) := by
  classical
  obtain ⟨CF, hCF, hFeas⟩ := learned_price_feasible
  obtain ⟨CN, hCN, hNear⟩ := learned_price_near_optimal
  have hmax : 0 < max CF CN := hCF.trans_le (le_max_left _ _)
  refine ⟨max CF CN, 15, hmax, by norm_num, ?_⟩
  intro m n E I rule hm hE hn hdvd hgp hvalid hcap
  have heps := TCSShortlistDLAMain.LearnedPrices.eps_pos E
  have hL := log_population_accuracy_ge_one hn hE hdvd
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let K : ℝ := (m : ℝ) * Real.log ((n : ℝ) / eps E) / (eps E) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcapF (i : Fin m) :
      CF * (m : ℝ) * Real.log ((n : ℝ) / eps E) / (eps E) ^ 2 ≤ I.b i := by
    calc
      _ = CF * K := by dsimp [K]; ring
      _ ≤ max CF CN * K := mul_le_mul_of_nonneg_right (le_max_left _ _) hK
      _ = _ := by dsimp [K]; ring
      _ ≤ I.b i := hcap i
  have hcapN (i : Fin m) :
      CN * (m : ℝ) * Real.log ((n : ℝ) / eps E) / (eps E) ^ 2 ≤ I.b i := by
    calc
      _ = CN * K := by dsimp [K]; ring
      _ ≤ max CF CN * K := mul_le_mul_of_nonneg_right (le_max_right _ _) hK
      _ = _ := by dsimp [K]; ring
      _ ≤ I.b i := hcap i
  have hb (i : Fin m) : 0 ≤ I.b i := by
    calc
      0 ≤ max CF CN * K := mul_nonneg hmax.le hK
      _ = _ := by dsimp [K]; ring
      _ ≤ I.b i := hcap i
  let F : Equiv.Perm (Fin n) → Prop := fun σ ↦
    ∀ ℓ ∈ phases n E, ∀ i : Fin m,
      (∑ t ∈ univ.filter (fun t : Fin n ↦ ℓ ≤ t.val ∧ t.val < 2 * ℓ),
        I.arrA σ t i * threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t) ≤
          ((ℓ : ℝ) / n) * I.b i
  let N : Equiv.Perm (Fin n) → Prop := fun σ ↦
    ∀ ℓ ∈ phases n E,
      (1 - 2 * slack n E ℓ - eps E) *
          I.partialOPT σ (2 * ℓ) (fun i ↦ (2 * (ℓ : ℝ) / n) * I.b i) ≤
        ∑ t ∈ firstTimes n (2 * ℓ),
          I.arrPi σ t * threshold (I.arrPi σ) (I.arrA σ) (learnedPrice I rule E σ ℓ) t
  let G : Equiv.Perm (Fin n) → Prop := fun σ ↦ F σ ∧ N σ
  have hF : 1 - eps E ≤ probPerm F := hFeas m n E I rule hm hE hn hdvd hgp hvalid hcapF
  have hN : 1 - eps E ≤ probPerm N := hNear m n E I rule hm hE hn hdvd hgp hvalid hcapN
  have hG : 1 - 2 * eps E ≤ probPerm G := by
    have h := probPerm_and_ge F N
    change probPerm F + probPerm N - 1 ≤ probPerm G at h
    linarith
  let V : ℕ → Equiv.Perm (Fin n) → ℝ :=
    fun k σ ↦ I.partialOPT σ k (fun i ↦ (k : ℝ) / n * I.b i)
  let Loss : Equiv.Perm (Fin n) → ℝ := fun σ ↦
    V (learnLen n E) σ + ∑ ℓ ∈ phases n E, (2 * slack n E ℓ + eps E) * V (2 * ℓ) σ
  have hLoss0 (σ : Equiv.Perm (Fin n)) : 0 ≤ Loss σ := by
    apply add_nonneg (scaled_partialOPT_nonneg I σ _ hb)
    apply sum_nonneg
    intro ℓ _
    apply mul_nonneg _ (scaled_partialOPT_nonneg I σ _ hb)
    dsimp [slack]
    positivity
  have hpoint (σ : Equiv.Perm (Fin n)) (hσ : G σ) :
      I.OPT - Loss σ ≤ dlaValue I rule E σ := by
    have h := opt_sub_losses_le_dlaValue_of_phase_events I rule σ hn hE hdvd hvalid hb hσ.1 hσ.2
    change I.OPT - V (learnLen n E) σ -
      (∑ ℓ ∈ phases n E, (2 * slack n E ℓ + eps E) * V (2 * ℓ) σ) ≤
        dlaValue I rule E σ at h
    dsimp [Loss]
    linarith only [h]
  have hgood := good_event_loss_bound (fun σ ↦ dlaValue I rule E σ) Loss I.OPT G
    (fun σ ↦ TCSShortlistDLAMain.DLAExecution.dlaValue_nonneg I rule E σ) hLoss0 hpoint
  have hLoss : avgPerm Loss ≤ 13 * eps E * I.OPT := expected_partial_losses_le I hb hn hE hdvd
  have hO : 0 ≤ I.OPT := OPT_nonneg I hb
  have hprob : (1 - 2 * eps E) * I.OPT ≤ probPerm G * I.OPT :=
    mul_le_mul_of_nonneg_right hG hO
  calc
    (1 - 15 * eps E) * I.OPT = (1 - 2 * eps E) * I.OPT - 13 * eps E * I.OPT := by ring
    _ ≤ probPerm G * I.OPT - avgPerm Loss := sub_le_sub hprob hLoss
    _ ≤ avgPerm (fun σ ↦ dlaValue I rule E σ) := hgood
