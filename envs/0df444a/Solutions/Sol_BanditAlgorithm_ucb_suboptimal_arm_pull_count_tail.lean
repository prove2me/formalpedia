-- Prove2me | solution 1 for BanditAlgorithm.ucb_suboptimal_arm_pull_count_tail
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-07-19T02:48:21.668888+00:00
-- url     : https://prove2.me/submissions/610979b1-8315-4ad8-9793-bcff1ba9c630

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy
import Definitions.Def_ucbStoppedCenteredSum
import Theorems.Thm_BanditAlgorithm_ucb_pull_count_bad_event_inclusion
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
Direct work toward the remaining UCB pull-count tail theorem.  The construction
is the canonical-model exponential supermartingale corresponding to the
reward-stack/optional-stopping argument in Lattimore--Szepesvári §4.6 (printed
p. 65), Exercise 4.4 (printed p. 69), and Theorem 7.1, Eqs. (7.6)--(7.10)
(printed pp. 106--108).
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- Centered reward accumulated only on pulls of arm `i`. -/
noncomputable def armCenteredSum {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

/-- The exponential score whose one-step conditional mean is at most its
previous value for a 1-subgaussian arm. -/
noncomputable def armExpScore {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (θ : ℝ) (h : BanditHistory k n) : ℝ :=
  Real.exp
    (θ * armCenteredSum ν i h - θ ^ 2 / 2 * (armPullCount i h : ℝ))

theorem armPullCount_snoc_tail {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add]
  simp only [armPullCount]
  have hset (g : BanditHistory k n) :
      ({t | (g t).1 = i}.toFinset.card : ℝ) =
        ∑ t, if (g t).1 = i then 1 else 0 := by
    have hs : {t | (g t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (g t).1 = i) := by ext t; simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (g t).1 = i)
        Finset.univ).symm
  rw [hset]
  have hsnoc :
      (({t | (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset.card : ℕ) : ℝ) =
        ∑ t, if (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i then 1 else 0 := by
    have hs : {t | (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset =
        Finset.univ.filter
          (fun t ↦ (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin (n + 1) ↦
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i)
        Finset.univ).symm
  rw [hsnoc, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

theorem armCenteredSum_snoc {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    armCenteredSum ν i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSum ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSum, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

theorem measurable_armCenteredSum {k n : ℕ} (ν : StochasticBandit k)
    (i : Fin k) : Measurable (armCenteredSum (n := n) ν i) := by
  change Measurable (fun h : BanditHistory k n ↦
    ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0)
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  have hx : Measurable (fun h : BanditHistory k n ↦ (h t).2) :=
    measurable_snd.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    (hx.sub measurable_const) measurable_const

theorem measurable_armPullCount_cast_tail {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by ext t; simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    measurable_const measurable_const

theorem measurable_armExpScore {k n : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (θ : ℝ) : Measurable (armExpScore (n := n) ν i θ) := by
  exact ((measurable_const.mul (measurable_armCenteredSum ν i)).sub
    ((measurable_const.div measurable_const).mul
      (measurable_armPullCount_cast_tail i))).exp

theorem armExpScore_snoc {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (θ : ℝ) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armExpScore ν i θ (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armExpScore ν i θ h *
        Real.exp (if z.1 = i then
          θ * (z.2 - banditArmMean ν i) - θ ^ 2 / 2 else 0) := by
  rw [armExpScore, armExpScore, armCenteredSum_snoc,
    armPullCount_snoc_tail, Nat.cast_add]
  by_cases hz : z.1 = i
  · simp only [hz, if_pos, Nat.cast_one]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [hz]

/-- Under a deterministic arm selection, the canonical one-step law is the
pushforward of that arm's reward distribution. -/
theorem banditStepKernel_apply_eq_map_of_selected_tail
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    banditStepKernel ν π m h = (ν.P a).map (Prod.mk a) := by
  rw [banditStepKernel]
  ext s hs
  rw [Kernel.compProd_apply hs, hselect, lintegral_dirac]
  rw [Measure.map_apply measurable_prodMk_left hs]
  rw [Kernel.comap_apply]
  simp [banditRewardKernel, Kernel.ofFunOfCountable]

theorem banditStepKernel_ae_selected_arm_tail
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.1 = a := by
  rw [banditStepKernel_apply_eq_map_of_selected_tail ν π h a hselect]
  exact (ae_map_iff (μ := ν.P a) measurable_prodMk_left.aemeasurable
    (by measurability)).2 (Filter.Eventually.of_forall fun _ ↦ rfl)

theorem banditStepKernel_selected_centered_reward_subgaussian_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (π : BanditPolicy k) {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    HasSubgaussianMGF
      (fun z : Fin k × ℝ ↦ z.2 - banditArmMean ν z.1) 1
      (banditStepKernel ν π m h) := by
  rw [banditStepKernel_apply_eq_map_of_selected_tail ν π h a hselect]
  have ha := hν.2 a
  constructor
  · intro t
    have hmeas : AEStronglyMeasurable
        (fun z : Fin k × ℝ ↦ Real.exp
          (t * (z.2 - banditArmMean ν z.1)))
        ((ν.P a).map (Prod.mk a)) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    rw [integrable_map_measure hmeas measurable_prodMk_left.aemeasurable]
    exact ha.integrable_exp_mul t
  · intro t
    have hmeas : AEStronglyMeasurable
        (fun z : Fin k × ℝ ↦ Real.exp
          (t * (z.2 - banditArmMean ν z.1)))
        ((ν.P a).map (Prod.mk a)) := by
      apply Measurable.aestronglyMeasurable
      fun_prop
    rw [mgf_map measurable_prodMk_left.aemeasurable hmeas]
    have hm := ha.mgf_le t
    simp only [one_pow] at hm
    exact hm

/-- The fixed-arm centered increment has the exact predictable proxy: one if
UCB selects `i` at this history and zero otherwise. -/
theorem banditStepKernel_ucb_arm_increment_subgaussian_sharp_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (h : BanditHistory k m) (i : Fin k) :
    ∃ a : Fin k, (π.select m) h = Measure.dirac a ∧
      HasSubgaussianMGF
        (fun z : Fin k × ℝ ↦
          if z.1 = i then z.2 - banditArmMean ν i else 0)
        (if a = i then 1 else 0) (banditStepKernel ν π m h) := by
  obtain ⟨a, hselect, _⟩ := hπ m h
  refine ⟨a, hselect, ?_⟩
  have hae := banditStepKernel_ae_selected_arm_tail ν π h a hselect
  by_cases hai : a = i
  · subst a
    have heq : (fun z : Fin k × ℝ ↦ z.2 - banditArmMean ν z.1) =ᵐ[
        banditStepKernel ν π m h]
        (fun z ↦ if z.1 = i then z.2 - banditArmMean ν i else 0) := by
      filter_upwards [hae] with z hz
      simp [hz]
    simpa only [if_pos] using
      (banditStepKernel_selected_centered_reward_subgaussian_tail
        ν hν π h i hselect).congr heq
  · simp only [if_neg hai]
    have hzero : HasSubgaussianMGF (fun _ : Fin k × ℝ ↦ 0) 0
        (banditStepKernel ν π m h) := HasSubgaussianMGF.fun_zero
    apply hzero.congr
    filter_upwards [hae] with z hz
    simp [hz, hai]

theorem banditStepKernel_ucb_arm_increment_mgf_le_selection_probability_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (h : BanditHistory k m) (i : Fin k) (t : ℝ) :
    mgf (fun z : Fin k × ℝ ↦
        if z.1 = i then z.2 - banditArmMean ν i else 0)
        (banditStepKernel ν π m h) t ≤
      Real.exp ((π.select m h).real {i} * t ^ 2 / 2) := by
  obtain ⟨a, hselect, hsub⟩ :=
    banditStepKernel_ucb_arm_increment_subgaussian_sharp_tail ν hν hπ h i
  have hm := hsub.mgf_le t
  rw [hselect]
  have hprob : (Measure.dirac a).real {i} = if a = i then 1 else 0 := by
    rw [Measure.real]
    by_cases hai : a = i
    · subst a
      simp
    · simp [hai]
  rw [hprob]
  by_cases hai : a = i
  · simpa [hai] using hm
  · simpa [hai] using hm

/-- One-step exponential-supermartingale inequality with the exact
predictable selection-probability compensator. -/
theorem banditStepKernel_integral_exp_arm_increment_compensated_le_one_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (h : BanditHistory k m) (i : Fin k) (t : ℝ) :
    ∫ z, Real.exp
        (t * (if z.1 = i then z.2 - banditArmMean ν i else 0) -
          (π.select m h).real {i} * t ^ 2 / 2)
        ∂banditStepKernel ν π m h ≤ 1 := by
  let X : Fin k × ℝ → ℝ := fun z ↦
    if z.1 = i then z.2 - banditArmMean ν i else 0
  let q : ℝ := (π.select m h).real {i}
  have hmgf :=
    banditStepKernel_ucb_arm_increment_mgf_le_selection_probability_tail
      ν hν hπ h i t
  have hconst : 0 ≤ Real.exp (-q * t ^ 2 / 2) := Real.exp_nonneg _
  calc
    (∫ z, Real.exp (t * X z - q * t ^ 2 / 2)
        ∂banditStepKernel ν π m h) =
        Real.exp (-q * t ^ 2 / 2) *
          mgf X (banditStepKernel ν π m h) t := by
      have heq : (fun z ↦ Real.exp (t * X z - q * t ^ 2 / 2)) =
          fun z ↦ Real.exp (-q * t ^ 2 / 2) * Real.exp (t * X z) := by
        funext z
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq, integral_const_mul]
      rfl
    _ ≤ Real.exp (-q * t ^ 2 / 2) * Real.exp (q * t ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left (by simpa [X, q] using hmgf) hconst
    _ = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp

theorem integrable_banditStepKernel_exp_arm_increment_compensated_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (h : BanditHistory k m) (i : Fin k) (t : ℝ) :
    Integrable (fun z ↦ Real.exp
        (t * (if z.1 = i then z.2 - banditArmMean ν i else 0) -
          (π.select m h).real {i} * t ^ 2 / 2))
      (banditStepKernel ν π m h) := by
  let X : Fin k × ℝ → ℝ := fun z ↦
    if z.1 = i then z.2 - banditArmMean ν i else 0
  let q : ℝ := (π.select m h).real {i}
  obtain ⟨a, hselect, hsharp⟩ :=
    banditStepKernel_ucb_arm_increment_subgaussian_sharp_tail ν hν hπ h i
  have hbase := hsharp.integrable_exp_mul t
  have heq : (fun z ↦ Real.exp (t * X z - q * t ^ 2 / 2)) =
      fun z ↦ Real.exp (-q * t ^ 2 / 2) * Real.exp (t * X z) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (fun z ↦ Real.exp
      (t * (if z.1 = i then z.2 - banditArmMean ν i else 0) -
        (π.select m h).real {i} * t ^ 2 / 2)) =
      (fun z ↦ Real.exp (t * X z - q * t ^ 2 / 2)) by rfl]
  rw [heq]
  exact hbase.const_mul _

theorem measurable_ucb_selection_probability_tail
    {k m : ℕ} (π : BanditPolicy k) (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ (π.select m h).real {i}) := by
  exact (Kernel.measurable_coe (π.select m)
    (measurableSet_singleton i)).ennreal_toReal

theorem banditStepKernel_ae_arm_indicator_eq_selection_probability_tail
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    {δ : ℝ} (hπ : IsUCBPolicy δ π) {m : ℕ}
    (h : BanditHistory k m) (i : Fin k) :
    ∀ᵐ z ∂banditStepKernel ν π m h,
      (if z.1 = i then (1 : ℝ) else 0) = (π.select m h).real {i} := by
  obtain ⟨a, hselect, _⟩ := hπ m h
  have hae := banditStepKernel_ae_selected_arm_tail ν π h a hselect
  have hprob : (π.select m h).real {i} = if a = i then 1 else 0 := by
    rw [hselect, Measure.real]
    by_cases hai : a = i
    · subst a
      simp
    · simp [hai]
  filter_upwards [hae] with z hz
  rw [hprob, hz]

/-- Sum of the predictable one-step probabilities of selecting arm `i` along
the prefixes of a history. -/
noncomputable def ucbSelectionProxySumTail {k : ℕ} (π : BanditPolicy k)
    (i : Fin k) : ∀ n, BanditHistory k n → ℝ
  | 0, _ => 0
  | n + 1, h =>
      ucbSelectionProxySumTail π i n (Fin.init h) +
        (π.select n (Fin.init h)).real {i}

theorem measurable_ucbSelectionProxySumTail {k : ℕ} (π : BanditPolicy k)
    (i : Fin k) : ∀ n, Measurable (ucbSelectionProxySumTail π i n) := by
  intro n
  induction n with
  | zero => simp [ucbSelectionProxySumTail]
  | succ n ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (n + 1) ↦ Fin.init h) := by
        fun_prop
      exact (ih.comp hinit).add
        ((measurable_ucb_selection_probability_tail π i).comp hinit)

/-- The exact predictable variance proxy is the realized pull count almost
surely.  This is the canonical-model replacement for exposing an independent
reward stack. -/
theorem banditMeasure_ae_ucbSelectionProxySumTail_eq_pullCount
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    {δ : ℝ} (hπ : IsUCBPolicy δ π) (i : Fin k) :
    ∀ n, ∀ᵐ h ∂banditMeasure ν π n,
      ucbSelectionProxySumTail π i n h = armPullCount i h := by
  intro n
  induction n with
  | zero =>
      filter_upwards [] with h
      simp [ucbSelectionProxySumTail, armPullCount]
  | succ n ih =>
      have hset : MeasurableSet
          {h : BanditHistory k (n + 1) |
            ucbSelectionProxySumTail π i (n + 1) h = armPullCount i h} :=
        (measurable_ucbSelectionProxySumTail π i (n + 1)).stronglyMeasurable.measurableSet_eq_fun
          (measurable_armPullCount_cast_tail i).stronglyMeasurable
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih] with h hh
        filter_upwards [banditStepKernel_ae_arm_indicator_eq_selection_probability_tail
          ν hπ h i] with z hz
        simp [ucbSelectionProxySumTail, armPullCount_snoc_tail, hh, ← hz]

theorem banditStepKernel_ae_scoreFactor_eq_compensated_tail
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    {δ : ℝ} (hπ : IsUCBPolicy δ π) {m : ℕ}
    (h : BanditHistory k m) (i : Fin k) (t : ℝ) :
    (fun z : Fin k × ℝ ↦ Real.exp
      (if z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)) =ᵐ[
        banditStepKernel ν π m h]
      (fun z ↦ Real.exp
        (t * (if z.1 = i then z.2 - banditArmMean ν i else 0) -
          (π.select m h).real {i} * t ^ 2 / 2)) := by
  filter_upwards [banditStepKernel_ae_arm_indicator_eq_selection_probability_tail
    ν hπ h i] with z hz
  by_cases hzi : z.1 = i
  · simp only [hzi, if_pos] at hz ⊢
    rw [← hz]
    simp
  · simp only [hzi, if_neg] at hz ⊢
    rw [← hz]
    simp

theorem integrable_banditStepKernel_armScoreFactor_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (h : BanditHistory k m) (i : Fin k) (t : ℝ) :
    Integrable (fun z : Fin k × ℝ ↦ Real.exp
      (if z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0))
      (banditStepKernel ν π m h) := by
  exact (integrable_banditStepKernel_exp_arm_increment_compensated_tail
    ν hν hπ h i t).congr
      (banditStepKernel_ae_scoreFactor_eq_compensated_tail ν hπ h i t).symm

theorem banditStepKernel_integral_armScoreFactor_le_one_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (h : BanditHistory k m) (i : Fin k) (t : ℝ) :
    ∫ z : Fin k × ℝ, Real.exp
      (if z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
      ∂banditStepKernel ν π m h ≤ 1 := by
  rw [integral_congr_ae
    (banditStepKernel_ae_scoreFactor_eq_compensated_tail ν hπ h i t)]
  exact banditStepKernel_integral_exp_arm_increment_compensated_le_one_tail
    ν hν hπ h i t

theorem integral_armExpScore_zero_tail
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (t : ℝ) :
    ∫ h, armExpScore ν i t h ∂banditMeasure ν π 0 = 1 := by
  simp [banditMeasure, armExpScore, armCenteredSum, armPullCount]

theorem measurable_armScoreFactor_tail {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (t : ℝ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ Real.exp
      (if p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)) := by
  apply Measurable.exp
  exact Measurable.ite
    ((measurableSet_singleton i).preimage measurable_snd.fst)
    ((measurable_snd.snd.sub measurable_const).const_mul t |>.sub measurable_const)
    measurable_const

/-- The old exponential score times its one-step factor is integrable under
the canonical composition-product whenever the old score is integrable. -/
theorem integrable_compProd_armExpScore_factor_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (μ : Measure (BanditHistory k m)) [IsProbabilityMeasure μ]
    (i : Fin k) (t : ℝ)
    (hold : Integrable (armExpScore ν i t : BanditHistory k m → ℝ) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      armExpScore ν i t p.1 * Real.exp
        (if p.2.1 = i then
          t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    armExpScore ν i t p.1 * Real.exp
      (if p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_armExpScore ν i t).comp measurable_fst).mul
      (measurable_armScoreFactor_tail ν i t)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_banditStepKernel_armScoreFactor_tail ν hν hπ h i t).const_mul
        (armExpScore ν i t h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ armExpScore ν i t h := Real.exp_nonneg _
    have hcond := banditStepKernel_integral_armScoreFactor_le_one_tail
      ν hν hπ h i t
    have hinner_nonneg : 0 ≤
        ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖armExpScore ν i t h * Real.exp
      (if z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)‖
      ∂banditStepKernel ν π m h) ≤ ‖armExpScore ν i t h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

/-- The fixed-arm exponential score is a finite-horizon supermartingale in
expectation.  Its variance proxy is the realized pull count rather than the
ambient horizon. -/
theorem armExpScore_integrable_and_integral_le_one_tail
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (i : Fin k) (t : ℝ) : ∀ n : ℕ,
    Integrable (armExpScore ν i t : BanditHistory k n → ℝ)
      (banditMeasure ν π n) ∧
    ∫ h, armExpScore ν i t h ∂banditMeasure ν π n ≤ 1 := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp [banditMeasure, armExpScore, armCenteredSum, armPullCount]
      · simp [banditMeasure, armExpScore, armCenteredSum, armPullCount]
  | succ n ih =>
      let μ := banditMeasure ν π n
      let κ := banditStepKernel ν π n
      let snoc : BanditHistory k n × (Fin k × ℝ) → BanditHistory k (n + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k n × (Fin k × ℝ) → ℝ := fun p ↦
        armExpScore ν i t p.1 * Real.exp
          (if p.2.1 = i then
            t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
      have hrewrite : (fun p ↦ armExpScore ν i t (snoc p)) = F := by
        funext p
        exact armExpScore_snoc ν i t p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) := by
        exact integrable_compProd_armExpScore_factor_tail
          ν hν hπ μ i t ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_armExpScore (n := n + 1) ν i t).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable (fun p ↦ armExpScore ν i t (snoc p)) (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_armExpScore (n := n + 1) ν i t).aestronglyMeasurable]
        change (∫ p, armExpScore ν i t (snoc p) ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, armExpScore ν i t h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, armExpScore ν i t h * Real.exp
              (if z.1 = i then
                t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
              ∂κ h) ≤ armExpScore ν i t h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_armScoreFactor_le_one_tail
                ν hν hπ h i t)
          _ ≤ 1 := ih.2

/-- Adaptive Chernoff bound at a deterministic pull cap.  This is the sharp
fixed-arm concentration consequence needed after stopping at the `u`-th pull
in L&S Eqs. (7.7)--(7.9). -/
theorem armCenteredSum_tail_at_pull_cap
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * t ≤ armCenteredSum ν i h ∧ armPullCount i h ≤ u} ≤
      Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    armCenteredSum ν i h - t / 2 * (armPullCount i h : ℝ)
  have hscore := armExpScore_integrable_and_integral_le_one_tail
    ν hν hπ i t n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp (t * X h)) =
      armExpScore ν i t := by
    funext h
    rw [armExpScore]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable (fun h : BanditHistory k n ↦ Real.exp (t * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) ht hint
  calc
    μ.real {h : BanditHistory k n |
        (u : ℝ) * t ≤ armCenteredSum ν i h ∧ armPullCount i h ≤ u} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      change (u : ℝ) * t ≤ armCenteredSum ν i h ∧ armPullCount i h ≤ u at hh
      have hT : (armPullCount i h : ℝ) ≤ u := by exact_mod_cast hh.2
      dsimp [X]
      nlinarith [hh.1, mul_nonneg ht (sub_nonneg.mpr hT)]
    _ ≤ Real.exp (-t * ((u : ℝ) * t / 2)) * mgf X μ t := hchern
    _ ≤ Real.exp (-t * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
      congr 1
      ring

/-! The stopped reward stack used in L&S Eqs. (7.7)--(7.9).  Unlike
`armCenteredSum`, this process ignores rewards after the first `u` pulls of the
chosen arm.  It is defined recursively so its one-step predictable increment
is visible to the canonical `compProd` construction. -/

theorem armStoppedCenteredSum_snoc {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

theorem min_armPullCount_snoc {k m : ℕ} (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    min (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)) u =
      min (armPullCount i h) u +
        if armPullCount i h < u ∧ z.1 = i then 1 else 0 := by
  rw [armPullCount_snoc_tail]
  by_cases hi : z.1 = i
  · by_cases hlt : armPullCount i h < u
    · simp [hi, hlt]
      omega
    · simp [hi, hlt]
      omega
  · simp [hi]

theorem measurable_armStoppedCenteredSum {k : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) (m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable (fun h : BanditHistory k (m + 1) ↦
          (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_cast_tail i).comp hinit
      have hlt : MeasurableSet {h : BanditHistory k (m + 1) |
          armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet {h : BanditHistory k (m + 1) |
          (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

noncomputable def armStoppedExpScore {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) (t : ℝ) (h : BanditHistory k m) : ℝ :=
  Real.exp (t * armStoppedCenteredSum ν i u m h -
    t ^ 2 / 2 * ((min (armPullCount i h) u : ℕ) : ℝ))

theorem measurable_armStoppedExpScore {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable (armStoppedExpScore ν i u t : BanditHistory k m → ℝ) := by
  apply Measurable.exp
  apply (measurable_const.mul (measurable_armStoppedCenteredSum ν i u m)).sub
  have hmin : Measurable (fun h : BanditHistory k m ↦
      min (armPullCount i h : ℝ) (u : ℝ)) :=
    (measurable_armPullCount_cast_tail i).min measurable_const
  have h2 : Measurable (fun h : BanditHistory k m ↦
      t ^ 2 / 2 * min (armPullCount i h : ℝ) (u : ℝ)) := measurable_const.mul hmin
  simpa only [Nat.cast_min] using h2

theorem armStoppedExpScore_snoc {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) (t : ℝ) (h : BanditHistory k m)
    (z : Fin k × ℝ) :
    armStoppedExpScore ν i u t
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedExpScore ν i u t h *
        Real.exp (if armPullCount i h < u ∧ z.1 = i then
          t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0) := by
  rw [armStoppedExpScore, armStoppedExpScore,
    armStoppedCenteredSum_snoc, min_armPullCount_snoc, Nat.cast_add]
  by_cases hlt : armPullCount i h < u
  · by_cases hi : z.1 = i
    · simp only [hlt, hi, and_self, if_pos, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [hlt, hi]
  · simp [hlt]

theorem integrable_banditStepKernel_stoppedScoreFactor
    {k m : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    Integrable (fun z : Fin k × ℝ ↦ Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0))
      (banditStepKernel ν π m h) := by
  by_cases hlt : armPullCount i h < u
  · simpa [hlt] using
      integrable_banditStepKernel_armScoreFactor_tail ν hν hπ h i t
  · simp [hlt]

theorem banditStepKernel_integral_stoppedScoreFactor_le_one
    {k m : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    ∫ z : Fin k × ℝ, Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
      ∂banditStepKernel ν π m h ≤ 1 := by
  by_cases hlt : armPullCount i h < u
  · simpa [hlt] using
      banditStepKernel_integral_armScoreFactor_le_one_tail ν hν hπ h i t
  · simp [hlt]

theorem measurable_stoppedScoreFactor {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)) := by
  apply Measurable.exp
  have hcount : Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      (armPullCount i p.1 : ℝ)) :=
    (measurable_armPullCount_cast_tail i).comp measurable_fst
  have hlt : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | armPullCount i p.1 < u} := by
    simpa only [Nat.cast_lt] using measurableSet_lt hcount
      (measurable_const : Measurable
        (fun _ : BanditHistory k m × (Fin k × ℝ) ↦ (u : ℝ)))
  have heq : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} :=
    (measurableSet_singleton i).preimage measurable_snd.fst
  exact Measurable.ite (hlt.inter heq)
    ((measurable_snd.snd.sub measurable_const).const_mul t |>.sub measurable_const)
    measurable_const

theorem integrable_compProd_armStoppedExpScore_factor
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    {m : ℕ} (μ : Measure (BanditHistory k m)) [IsProbabilityMeasure μ]
    (i : Fin k) (u : ℕ) (t : ℝ)
    (hold : Integrable
      (armStoppedExpScore ν i u t : BanditHistory k m → ℝ) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      armStoppedExpScore ν i u t p.1 * Real.exp
        (if armPullCount i p.1 < u ∧ p.2.1 = i then
          t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    armStoppedExpScore ν i u t p.1 * Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_armStoppedExpScore ν i u t).comp measurable_fst).mul
      (measurable_stoppedScoreFactor ν i u t)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_banditStepKernel_stoppedScoreFactor
        ν hν hπ h i u t).const_mul (armStoppedExpScore ν i u t h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ armStoppedExpScore ν i u t h := Real.exp_nonneg _
    have hcond := banditStepKernel_integral_stoppedScoreFactor_le_one
      ν hν hπ h i u t
    have hinner_nonneg : 0 ≤ ∫ z, ‖G (h, z)‖
        ∂banditStepKernel ν π m h := integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖armStoppedExpScore ν i u t h * Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)‖
      ∂banditStepKernel ν π m h) ≤ ‖armStoppedExpScore ν i u t h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

theorem armStoppedExpScore_integrable_and_integral_le_one
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (i : Fin k) (u : ℕ) (t : ℝ) : ∀ m : ℕ,
    Integrable (armStoppedExpScore ν i u t : BanditHistory k m → ℝ)
      (banditMeasure ν π m) ∧
    ∫ h, armStoppedExpScore ν i u t h ∂banditMeasure ν π m ≤ 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;>
        simp [banditMeasure, armStoppedExpScore, armStoppedCenteredSum,
          armPullCount]
  | succ m ih =>
      let μ := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        armStoppedExpScore ν i u t p.1 * Real.exp
          (if armPullCount i p.1 < u ∧ p.2.1 = i then
            t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
      have hrewrite : (fun p ↦ armStoppedExpScore ν i u t (snoc p)) = F := by
        funext p
        exact armStoppedExpScore_snoc ν i u t p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) :=
        integrable_compProd_armStoppedExpScore_factor ν hν hπ μ i u t ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_armStoppedExpScore (m := m + 1) ν i u t).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable (fun p ↦ armStoppedExpScore ν i u t (snoc p))
          (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_armStoppedExpScore
              (m := m + 1) ν i u t).aestronglyMeasurable]
        change (∫ p, armStoppedExpScore ν i u t (snoc p)
          ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, armStoppedExpScore ν i u t h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, armStoppedExpScore ν i u t h * Real.exp
              (if armPullCount i h < u ∧ z.1 = i then
                t * (z.2 - banditArmMean ν i) - t ^ 2 / 2 else 0)
              ∂κ h) ≤ armStoppedExpScore ν i u t h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_stoppedScoreFactor_le_one
                ν hν hπ h i u t)
          _ ≤ 1 := ih.2

theorem armStoppedCenteredSum_upper_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
      Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore := armStoppedExpScore_integrable_and_integral_le_one
    ν hν hπ i u t n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp (t * X h)) =
      armStoppedExpScore ν i u t := by
    funext h
    rw [armStoppedExpScore]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable (fun h : BanditHistory k n ↦ Real.exp (t * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) ht hint
  calc
    μ.real {h : BanditHistory k n |
        (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh _)
    _ ≤ Real.exp (-t * ((u : ℝ) * t / 2)) * mgf X μ t := hchern
    _ ≤ Real.exp (-t * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
      congr 1
      ring

theorem armStoppedCenteredSum_lower_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {δ : ℝ} (hπ : IsUCBPolicy δ π)
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
      Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    -armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore := armStoppedExpScore_integrable_and_integral_le_one
    ν hν hπ i u (-t) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp (t * X h)) =
      armStoppedExpScore ν i u (-t) := by
    funext h
    rw [armStoppedExpScore]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable (fun h : BanditHistory k n ↦ Real.exp (t * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) ht hint
  calc
    μ.real {h : BanditHistory k n |
        armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      change armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t at hh
      have hh' : (u : ℝ) * t ≤ -armStoppedCenteredSum ν i u n h := by
        linarith
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh' _)
    _ ≤ Real.exp (-t * ((u : ℝ) * t / 2)) * mgf X μ t := hchern
    _ ≤ Real.exp (-t * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-(u : ℝ) * t ^ 2 / 2) := by
      congr 1
      ring

theorem armStoppedCenteredSum_eq_armCenteredSum_of_pullCount_le
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h = armCenteredSum ν i h := by
  induction m with
  | zero => simp [armStoppedCenteredSum, armCenteredSum]
  | succ m ih =>
      rw [← Fin.snoc_init_self h] at hcount ⊢
      rw [armPullCount_snoc_tail] at hcount
      rw [armStoppedCenteredSum_snoc, armCenteredSum_snoc]
      by_cases hi : (h (Fin.last m)).1 = i
      · have hprev : armPullCount i (Fin.init h) < u := by
          simp [hi] at hcount
          omega
        rw [if_pos ⟨hprev, hi⟩, if_pos hi,
          ih (Fin.init h) (Nat.le_of_lt hprev)]
      · have hprev : armPullCount i (Fin.init h) ≤ u := by
          simpa [hi] using hcount
        rw [if_neg (fun hc ↦ hi hc.2), if_neg hi, ih (Fin.init h) hprev]

theorem armStoppedCenteredSum_snoc_of_cap_reached
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ)
    (hcap : u ≤ armPullCount i h) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h := by
  rw [armStoppedCenteredSum_snoc]
  simp [Nat.not_lt.mpr hcap]

theorem suboptimal_arm_stopped_cap_tail_le_inverse_square
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) (hn : 0 < n) :
    let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * (banditGap ν i / 2) ≤
            armStoppedCenteredSum ν i u n h} ≤
      1 / (n : ℝ) ^ 2 := by
  dsimp
  let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
  have hgap : 0 < (banditGap ν i) ^ 2 := sq_pos_of_pos hi
  have hu : 16 * Real.log n / (banditGap ν i) ^ 2 ≤ (u : ℝ) := by
    exact Nat.le_ceil _
  have hmul : 16 * Real.log n ≤ (u : ℝ) * (banditGap ν i) ^ 2 := by
    exact (div_le_iff₀ hgap).mp hu
  have harg : -(u : ℝ) * (banditGap ν i / 2) ^ 2 / 2 ≤
      -2 * Real.log n := by
    nlinarith
  calc
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * (banditGap ν i / 2) ≤
            armStoppedCenteredSum ν i u n h} ≤
        Real.exp (-(u : ℝ) * (banditGap ν i / 2) ^ 2 / 2) :=
      armStoppedCenteredSum_upper_tail ν hν hπ i u (le_of_lt (half_pos hi))
    _ ≤ Real.exp (-2 * Real.log n) := Real.exp_le_exp.mpr harg
    _ = 1 / (n : ℝ) ^ 2 := by
      rw [show -2 * Real.log (n : ℝ) =
        -Real.log (n : ℝ) + -Real.log (n : ℝ) by ring]
      rw [Real.exp_add, Real.exp_neg,
        Real.exp_log (by positivity : (0 : ℝ) < n)]
      field_simp

theorem stopped_cap_lower_confidence_tail_le_inverse_square
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (j : Fin k) (s : ℕ) (hs : 0 < s) (hn : 0 < n) :
    let t : ℝ := Real.sqrt
      (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t} ≤
      1 / (n : ℝ) ^ 2 := by
  dsimp
  let t : ℝ := Real.sqrt
    (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 ≤ Real.log ((n : ℝ) ^ 2) := by
    apply Real.log_nonneg
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hins : 0 ≤ 2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hlog) (le_of_lt hsreal)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht_sq : t ^ 2 = 2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ) := by
    exact Real.sq_sqrt hins
  have harg : -(s : ℝ) * t ^ 2 / 2 = -Real.log ((n : ℝ) ^ 2) := by
    rw [ht_sq]
    field_simp
  calc
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t} ≤
        Real.exp (-(s : ℝ) * t ^ 2 / 2) :=
      armStoppedCenteredSum_lower_tail ν hν hπ j s ht
    _ = Real.exp (-Real.log ((n : ℝ) ^ 2)) := by rw [harg]
    _ = 1 / (n : ℝ) ^ 2 := by
      rw [Real.exp_neg, Real.exp_log (sq_pos_of_pos hnreal)]
      field_simp

theorem optimal_arm_stopped_confidence_union_le_inverse
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (j : Fin k) (hn : 0 < n) :
    let bad : Fin n → Set (BanditHistory k n) := fun r ↦
      let s : ℕ := r + 1
      let t : ℝ := Real.sqrt
        (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
      {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
    (banditMeasure ν π n).real (⋃ r, bad r) ≤ 1 / (n : ℝ) := by
  dsimp
  let bad : Fin n → Set (BanditHistory k n) := fun r ↦
    let s : ℕ := r + 1
    let t : ℝ := Real.sqrt
      (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
    {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
  calc
    (banditMeasure ν π n).real (⋃ r, bad r) ≤
        ∑ r : Fin n, (banditMeasure ν π n).real (bad r) :=
      measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _r : Fin n, 1 / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact stopped_cap_lower_confidence_tail_le_inverse_square
        ν hν hπ j (r + 1) (Nat.succ_pos r) hn
    _ = 1 / (n : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      rw [Fintype.card_fin]
      field_simp

theorem armCenteredSum_eq_pullCount_mul_empirical_sub_mean
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k m) :
    armCenteredSum ν i h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSum, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

theorem ucb_two_bad_events_probability_le
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i j : Fin k) (hi : 0 < banditGap ν i) (hn : 0 < n) :
    let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
    let optBad : Fin n → Set (BanditHistory k n) := fun r ↦
      let s : ℕ := r + 1
      let t : ℝ := Real.sqrt
        (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
      {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
    let subBad : Set (BanditHistory k n) :=
      {h | (u : ℝ) * (banditGap ν i / 2) ≤
        armStoppedCenteredSum ν i u n h}
    (banditMeasure ν π n).real ((⋃ r, optBad r) ∪ subBad) ≤
      1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  dsimp
  let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
  let optBad : Fin n → Set (BanditHistory k n) := fun r ↦
    let s : ℕ := r + 1
    let t : ℝ := Real.sqrt
      (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
    {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
  let subBad : Set (BanditHistory k n) :=
    {h | (u : ℝ) * (banditGap ν i / 2) ≤
      armStoppedCenteredSum ν i u n h}
  calc
    (banditMeasure ν π n).real ((⋃ r, optBad r) ∪ subBad) ≤
        (banditMeasure ν π n).real (⋃ r, optBad r) +
          (banditMeasure ν π n).real subBad := measureReal_union_le _ _
    _ ≤ 1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := add_le_add
      (optimal_arm_stopped_confidence_union_le_inverse ν hν hπ j hn)
      (suboptimal_arm_stopped_cap_tail_le_inverse_square ν hν hπ i hi hn)

theorem ucb_pull_count_tail_of_ae_bad_event_inclusion
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i j : Fin k) (hi : 0 < banditGap ν i) (hn : 0 < n)
    (hinclude :
      let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
      let optBad : Fin n → Set (BanditHistory k n) := fun r ↦
        let s : ℕ := r + 1
        let t : ℝ := Real.sqrt
          (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
        {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
      let subBad : Set (BanditHistory k n) :=
        {h | (u : ℝ) * (banditGap ν i / 2) ≤
          armStoppedCenteredSum ν i u n h}
      ∀ᵐ h ∂banditMeasure ν π n,
        u < armPullCount i h → h ∈ ((⋃ r, optBad r) ∪ subBad)) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ < armPullCount i h} ≤
      1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
  let optBad : Fin n → Set (BanditHistory k n) := fun r ↦
    let s : ℕ := r + 1
    let t : ℝ := Real.sqrt
      (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
    {h | armStoppedCenteredSum ν j s n h ≤ -(s : ℝ) * t}
  let subBad : Set (BanditHistory k n) :=
    {h | (u : ℝ) * (banditGap ν i / 2) ≤
      armStoppedCenteredSum ν i u n h}
  have hmeasure : (banditMeasure ν π n).real
      {h : BanditHistory k n | u < armPullCount i h} ≤
      (banditMeasure ν π n).real ((⋃ r, optBad r) ∪ subBad) := by
    have hsub : ∀ᵐ h ∂banditMeasure ν π n,
        h ∈ {h : BanditHistory k n | u < armPullCount i h} →
          h ∈ ((⋃ r, optBad r) ∪ subBad) := by
      filter_upwards [hinclude] with h hh
      exact hh
    rw [Measure.real, Measure.real]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae hsub)
  exact hmeasure.trans (ucb_two_bad_events_probability_le
    ν hν hπ i j hi hn)

end BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 0 < k) {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν) {n : ℕ}
    (hn : 0 < n) (hkn : k < n)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < BanditAlgorithm.banditGap ν i) :
    (BanditAlgorithm.banditMeasure ν π n).real
        {h : BanditAlgorithm.BanditHistory k n |
          ⌈16 * Real.log n / (BanditAlgorithm.banditGap ν i) ^ 2⌉₊ <
            BanditAlgorithm.armPullCount i h} ≤
      1 / (n : ℝ) + 1 / (n : ℝ) ^ 2 := by
  obtain ⟨j, _hj, hinclude⟩ :=
    BanditAlgorithm.ucb_pull_count_bad_event_inclusion hk hn hkn hπ i hi
  exact BanditAlgorithm.ucb_pull_count_tail_of_ae_bad_event_inclusion
    ν hν hπ i j hi hn hinclude
