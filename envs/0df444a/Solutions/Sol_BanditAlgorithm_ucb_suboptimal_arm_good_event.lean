-- Prove2me | solution 1 for BanditAlgorithm.ucb_suboptimal_arm_good_event
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-18T23:47:01.661252+00:00
-- url     : https://prove2.me/submissions/5ea2ec17-4870-4c92-83c8-5e369bf23e2c

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy
import Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_pull_count_tail
import Mathlib.Data.Fintype.Order

/-!
Direct-proof work for Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020),
Theorem 7.1, printed pp. 105--108 (PDF pp. 114--117). The final theorem below
formalizes Eq. (7.5): a pull-count cap `u` on a measurable good event `G`, plus
the pathwise horizon cap `T_i(n) ≤ n`, gives
`E[T_i(n)] ≤ u + n P(Gᶜ)`.

The adaptive-sampling bridge used by the source is the reward-stack model in
§4.6, printed p. 65 (PDF p. 74), with equivalence to the canonical law assigned
as Exercise 4.4, printed p. 69 (PDF p. 78), whose hint invokes bounded optional
stopping.  In this file the measurable-event bridge, the complete `n = 1`
boundary, and the whole UCB initialization regime `n ≤ k` are proved without
`sorry`.  The exact remaining goal is isolated as the pull-count tail estimate
for `k < n`; its proof must construct or transport the reward-stack independent
samples before applying Mathlib's `measure_sum_range_ge_le_of_iIndepFun`.

An alternative formal route is Mathlib's
`measure_sum_ge_le_of_hasCondSubgaussianMGF` (Azuma--Hoeffding).  It avoids an
explicit reward-stack law, but still requires a filtration on fixed-horizon
histories and a proof that the stopped predictable reward increments are
conditionally subgaussian with total variance proxy at most `u`.  The current
platform definitions expose only the recursive kernel measure, so neither route
is a one-line reuse of the accepted fixed-sample confidence theorem.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem banditGap_nonneg {k : ℕ} (ν : StochasticBandit k) (i : Fin k) :
    0 ≤ banditGap ν i := by
  rw [banditGap, sub_nonneg]
  exact Finite.le_ciSup (fun j : Fin k ↦ banditArmMean ν j) i

theorem exists_optimal_arm {k : ℕ} (hk : 0 < k) (ν : StochasticBandit k) :
    ∃ j : Fin k, banditGap ν j = 0 := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨j, hj⟩ :=
    exists_eq_ciSup_of_finite (f := fun j : Fin k ↦ banditArmMean ν j)
  refine ⟨j, ?_⟩
  rw [banditGap, banditOptimalMean, ← hj]
  ring

theorem IsUCBPolicy.selects_unpulled {k : ℕ} {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m)
    (hex : ∃ j, armPullCount j h = 0) :
    ∃ a : Fin k, (π.select m) h = Measure.dirac a ∧ armPullCount a h = 0 := by
  obtain ⟨a, hdirac, hunpulled, _⟩ := hπ m h
  exact ⟨a, hdirac, hunpulled hex⟩

theorem IsUCBPolicy.selects_index_maximizer
    {k : ℕ} {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m)
    (hall : ∀ j, armPullCount j h ≠ 0) :
    ∃ a : Fin k, (π.select m) h = Measure.dirac a ∧
      ∀ j, ucbIndex δ j h ≤ ucbIndex δ a h := by
  obtain ⟨a, hdirac, _, hmax⟩ := hπ m h
  exact ⟨a, hdirac, hmax hall⟩

theorem IsUCBPolicy.selected_is_unpulled
    {k : ℕ} {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m) (i : Fin k)
    (hselect : (π.select m) h = Measure.dirac i)
    (hex : ∃ j, armPullCount j h = 0) : armPullCount i h = 0 := by
  obtain ⟨a, hdirac, hunpulled, _⟩ := hπ m h
  have hai : a = i := dirac_eq_dirac_iff.mp (hdirac.symm.trans hselect)
  simpa [hai] using hunpulled hex

theorem IsUCBPolicy.selected_index_dominates
    {k : ℕ} {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m) (i j : Fin k)
    (hselect : (π.select m) h = Measure.dirac i)
    (hall : ∀ a, armPullCount a h ≠ 0) :
    ucbIndex δ j h ≤ ucbIndex δ i h := by
  obtain ⟨a, hdirac, _, hmax⟩ := hπ m h
  have hai : a = i := dirac_eq_dirac_iff.mp (hdirac.symm.trans hselect)
  simpa [hai] using hmax hall j

theorem banditStepKernel_fst_eq_selected_dirac
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    (banditStepKernel ν π m).fst h = Measure.dirac a := by
  rw [banditStepKernel, Kernel.fst_compProd]
  exact hselect

theorem banditStepKernel_ae_selected_arm
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.1 = a := by
  let μ := banditStepKernel ν π m h
  have hfst : Measure.map Prod.fst μ = Measure.dirac a := by
    rw [← Kernel.fst_apply]
    exact banditStepKernel_fst_eq_selected_dirac ν π h a hselect
  have hmap : ∀ᵐ b ∂Measure.map Prod.fst μ, b = a := by
    rw [hfst]
    simp
  exact (ae_map_iff (μ := μ) measurable_fst.aemeasurable (by measurability)).1 hmap

theorem banditStepKernel_ae_obeys_ucb_rule
    {k : ℕ} {δ : ℝ} (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h,
      ((∃ j, armPullCount j h = 0) → armPullCount z.1 h = 0) ∧
      ((∀ j, armPullCount j h ≠ 0) →
        ∀ j, ucbIndex δ j h ≤ ucbIndex δ z.1 h) := by
  obtain ⟨a, hdirac, hunpulled, hmax⟩ := hπ m h
  filter_upwards [banditStepKernel_ae_selected_arm ν π h a hdirac] with z hz
  simpa [hz] using And.intro hunpulled hmax

private theorem pullCount_cast_eq_sum_indicator {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) = ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by ext t; simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

theorem sum_armPullCount {k n : ℕ} (h : BanditHistory k n) :
    ∑ i, armPullCount i h = n := by
  apply Nat.cast_injective (R := ℝ)
  push_cast
  simp_rw [pullCount_cast_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp

theorem exists_unpulled_of_history_length_lt_arms
    {k n : ℕ} (h : BanditHistory k n) (hnk : n < k) :
    ∃ i, armPullCount i h = 0 := by
  by_contra hex
  push_neg at hex
  have hle : k ≤ ∑ i, armPullCount i h := by
    calc
      k = ∑ _i : Fin k, 1 := by simp
      _ ≤ ∑ i, armPullCount i h :=
        Finset.sum_le_sum fun i _ ↦ Nat.one_le_iff_ne_zero.mpr (hex i)
  rw [sum_armPullCount] at hle
  omega

theorem armPullCount_snoc {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, pullCount_cast_eq_sum_indicator,
    pullCount_cast_eq_sum_indicator i h]
  rw [Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

theorem armPullCount_snoc_le_one_of_selected_unpulled
    {k n : ℕ} (h : BanditHistory k n) (z : Fin k × ℝ)
    (hcounts : ∀ j, armPullCount j h ≤ 1)
    (hnew : armPullCount z.1 h = 0) :
    ∀ j, armPullCount j (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) ≤ 1 := by
  intro j
  rw [armPullCount_snoc]
  by_cases hj : z.1 = j
  · subst j
    simp [hnew]
  · simp [hj, hcounts j]

theorem banditStepKernel_ae_preserves_initial_pull_caps
    {k : ℕ} {δ : ℝ} (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m)
    (hcounts : ∀ j, armPullCount j h ≤ 1)
    (hex : ∃ j, armPullCount j h = 0) :
    ∀ᵐ z ∂banditStepKernel ν π m h,
      ∀ j, armPullCount j (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) ≤ 1 := by
  filter_upwards [banditStepKernel_ae_obeys_ucb_rule ν hπ h] with z hz
  exact armPullCount_snoc_le_one_of_selected_unpulled h z hcounts (hz.1 hex)

theorem armPullCount_le_horizon {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) : armPullCount i h ≤ n := by
  change ({t | (h t).1 = i}.toFinset : Finset (Fin n)).card ≤ n
  simpa using
    (Finset.card_le_univ ({t | (h t).1 = i}.toFinset : Finset (Fin n)))

theorem integrable_armPullCount {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · simp_rw [pullCount_cast_eq_sum_indicator]
    have hm : Measurable (fun h : BanditHistory k n ↦
        ∑ t : Fin n, if (h t).1 = i then (1 : ℝ) else 0) := by
      apply Finset.measurable_sum
      intro t ht
      have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
        measurable_fst.comp (measurable_pi_apply t)
      exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
        measurable_const measurable_const
    exact hm.aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · exact_mod_cast armPullCount_le_horizon i h

/-- L&S Eq. (7.5), abstracted from the particular definition of the good event. -/
theorem expected_pullCount_le_good_cap_add_bad_probability
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (G : Set (BanditHistory k n)) (hG : MeasurableSet G)
    (u : ℕ) (hcap : ∀ h ∈ G, armPullCount i h ≤ u) :
    ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) ≤
      u + n * (banditMeasure ν π n).real Gᶜ := by
  let μ := banditMeasure ν π n
  let bad : BanditHistory k n → ℝ := Gᶜ.indicator (fun _ ↦ 1)
  have hT : Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) μ :=
    integrable_armPullCount ν π i
  have hbad : Integrable bad μ := by
    exact (integrable_const (1 : ℝ)).indicator hG.compl
  have hrhs : Integrable (fun h ↦ (u : ℝ) + n * bad h) μ :=
    (integrable_const (u : ℝ)).add (hbad.const_mul n)
  calc
    (∫ h, (armPullCount i h : ℝ) ∂μ) ≤
        ∫ h, ((u : ℝ) + n * bad h) ∂μ := by
      apply integral_mono hT hrhs
      intro h
      by_cases hh : h ∈ G
      · have hc : (armPullCount i h : ℝ) ≤ u := by exact_mod_cast hcap h hh
        simpa [bad, hh] using hc
      · have hc : (armPullCount i h : ℝ) ≤ n := by
          exact_mod_cast armPullCount_le_horizon i h
        have hu : (0 : ℝ) ≤ u := by positivity
        have hbad_one : bad h = 1 := by simp [bad, hh]
        change (armPullCount i h : ℝ) ≤ (u : ℝ) + (n : ℝ) * bad h
        rw [hbad_one, mul_one]
        linarith
    _ = (u : ℝ) + n * μ.real Gᶜ := by
      have hbadIntegral : ∫ h, bad h ∂μ = μ.real Gᶜ := by
        exact integral_indicator_one (μ := μ) hG.compl
      rw [integral_add (integrable_const (u : ℝ)) (hbad.const_mul n)]
      rw [integral_const, integral_const_mul]
      rw [hbadIntegral]
      simp [μ]

/-- The pull count, viewed as a real-valued random variable, is measurable. -/
theorem measurable_armPullCount_cast {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    exact pullCount_cast_eq_sum_indicator i h]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

/-- The event that arm `i` is pulled at most `u` times is measurable. -/
theorem measurableSet_armPullCount_le {k n : ℕ} (i : Fin k) (u : ℕ) :
    MeasurableSet {h : BanditHistory k n | armPullCount i h ≤ u} := by
  simpa only [Nat.cast_le] using
    (measurableSet_le (measurable_armPullCount_cast i)
      (measurable_const : Measurable (fun _ : BanditHistory k n ↦ (u : ℝ))))

/-- During UCB's initialization period, every arm has been pulled at most once.
This is the path-space version of the "initial period" observation immediately
before Lattimore--Szepesvári Eq. (7.6), printed pp. 105--106. -/
theorem banditMeasure_ae_initial_pull_caps
    {k m : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    {δ : ℝ} (hπ : IsUCBPolicy δ π) (hmk : m ≤ k) :
    ∀ᵐ h ∂banditMeasure ν π m, ∀ j, armPullCount j h ≤ 1 := by
  induction m with
  | zero =>
      filter_upwards [] with h
      intro j
      simp [armPullCount]
  | succ m ih =>
      have hm_le : m ≤ k := Nat.le_trans (Nat.le_succ m) hmk
      have hm_lt : m < k := Nat.lt_of_succ_le hmk
      have hset : MeasurableSet
          {h : BanditHistory k (m + 1) | ∀ j, armPullCount j h ≤ 1} := by
        convert MeasurableSet.iInter fun j ↦ measurableSet_armPullCount_le j 1 using 1
        ext h
        simp
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih hm_le] with h hcaps
        exact banditStepKernel_ae_preserves_initial_pull_caps ν hπ h hcaps
          (exists_unpulled_of_history_length_lt_arms h hm_lt)

/-- The UCB good-event theorem is already complete when the horizon does not
exceed the number of arms: initialization pulls each arm at most once, while
`n ≥ 2` makes the prescribed ceiling at least one. -/
theorem ucb_suboptimal_arm_good_event_of_horizon_le_arms
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n) (hn_two : 2 ≤ n)
    (hnk : n ≤ k) {π : BanditPolicy k}
    (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
    ∃ G : Set (BanditHistory k n),
      MeasurableSet G ∧
      (∀ h ∈ G, armPullCount i h ≤ u) ∧
      (banditMeasure ν π n).real Gᶜ ≤
        1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  dsimp
  have hn_one : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hn_one
  have hgap_sq : 0 < (banditGap ν i) ^ 2 := sq_pos_of_pos hi
  have hceil : 1 ≤ ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ := by
    rw [Nat.one_le_ceil_iff]
    exact div_pos (mul_pos (by norm_num) hlog) hgap_sq
  let G : Set (BanditHistory k n) :=
    {h | ∀ j, armPullCount j h ≤ 1}
  have hG : MeasurableSet G := by
    dsimp [G]
    convert MeasurableSet.iInter fun j ↦ measurableSet_armPullCount_le j 1 using 1
    ext h
    simp
  have hG_ae : ∀ᵐ h ∂banditMeasure ν π n, h ∈ G := by
    simpa [G] using banditMeasure_ae_initial_pull_caps ν hπ hnk
  refine ⟨G, hG, ?_, ?_⟩
  · intro h hh
    exact (hh i).trans hceil
  · have hzero : (banditMeasure ν π n) Gᶜ = 0 := mem_ae_iff.mp hG_ae
    rw [Measure.real, hzero]
    positivity

/-- A pull-count tail estimate supplies exactly the measurable good event used
in the source's Eqs. (7.5)--(7.10). -/
theorem good_event_of_pullCount_tail
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (u : ℕ) (b : ℝ)
    (hprob : (banditMeasure ν π n).real
        {h : BanditHistory k n | u < armPullCount i h} ≤ b) :
    ∃ G : Set (BanditHistory k n),
      MeasurableSet G ∧
      (∀ h ∈ G, armPullCount i h ≤ u) ∧
      (banditMeasure ν π n).real Gᶜ ≤ b := by
  refine ⟨{h | armPullCount i h ≤ u}, measurableSet_armPullCount_le i u,
    ?_, ?_⟩
  · intro h hh
    exact hh
  · simpa only [Set.compl_setOf, not_le] using hprob

/-- The explicit `n = 1` boundary of the UCB good-event child.  The empty good
event works because its complement has probability one and the claimed bound
is two. -/
theorem ucb_suboptimal_arm_good_event_n_one
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (1 : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    let u : ℕ := ⌈16 * Real.log 1 / (banditGap ν i) ^ 2⌉₊
    ∃ G : Set (BanditHistory k 1),
      MeasurableSet G ∧
      (∀ h ∈ G, armPullCount i h ≤ u) ∧
      (banditMeasure ν π 1).real Gᶜ ≤
        1 / (1 : ℝ) + 1 / (1 : ℝ) ^ 2 := by
  dsimp
  refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
  · intro h hh
    simp at hh
  · simp

/-- Complete exact-signature proof of the good-event child throughout the
initialization regime `n ≤ k`.  Consequently the only unresolved regime is
`k < n`, where the reward-stack concentration argument is genuinely needed. -/
theorem ucb_suboptimal_arm_good_event_of_horizon_le_arms_full
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n) (hnk : n ≤ k)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
    ∃ G : Set (BanditHistory k n),
      MeasurableSet G ∧
      (∀ h ∈ G, armPullCount i h ≤ u) ∧
      (banditMeasure ν π n).real Gᶜ ≤
        1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  by_cases hn_one : n = 1
  · subst n
    have hπ' : IsUCBPolicy (1 / (1 : ℝ) ^ 2) π := by simpa using hπ
    simpa using ucb_suboptimal_arm_good_event_n_one hk hν hπ' i hi
  · have hn_two : 2 ≤ n := by omega
    exact ucb_suboptimal_arm_good_event_of_horizon_le_arms
      hk hν hn hn_two hnk hπ i hi

/-- Exact assembly for the remaining direct proof.  After the fully proved
initialization regime, it is enough to establish the reward-stack pull-count
tail estimate in the post-initialization regime `k < n`.  This is precisely the
independence/optional-stopping bridge cited in L&S §4.6, printed p. 65, and
Exercise 4.4, printed p. 69, before the union bounds in Eqs. (7.7)--(7.10). -/
theorem ucb_suboptimal_arm_good_event_of_post_initialization_tail
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i)
    (hpost : k < n →
      (banditMeasure ν π n).real
          {h : BanditHistory k n |
            ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ < armPullCount i h} ≤
        1 / (n : ℝ) + 1 / (n : ℝ) ^ 2) :
    let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
    ∃ G : Set (BanditHistory k n),
      MeasurableSet G ∧
      (∀ h ∈ G, armPullCount i h ≤ u) ∧
      (banditMeasure ν π n).real Gᶜ ≤
        1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  by_cases hnk : n ≤ k
  · exact ucb_suboptimal_arm_good_event_of_horizon_le_arms_full
      hk hν hn hnk hπ i hi
  · exact good_event_of_pullCount_tail ν π i
      ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
      (1 / (n : ℝ) + 1 / (n : ℝ) ^ 2)
      (hpost (Nat.lt_of_not_ge hnk))

end BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 0 < k) {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < BanditAlgorithm.banditGap ν i) :
    let u : ℕ := ⌈16 * Real.log n / (BanditAlgorithm.banditGap ν i) ^ 2⌉₊
    ∃ G : Set (BanditAlgorithm.BanditHistory k n),
      MeasurableSet G ∧
      (∀ h ∈ G, BanditAlgorithm.armPullCount i h ≤ u) ∧
      (BanditAlgorithm.banditMeasure ν π n).real Gᶜ ≤
        1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  exact
    BanditAlgorithm.ucb_suboptimal_arm_good_event_of_post_initialization_tail
      hk hν hn hπ i hi
      (fun hkn ↦
        BanditAlgorithm.ucb_suboptimal_arm_pull_count_tail
          hk hν hn hkn hπ i hi)
