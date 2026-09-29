-- Prove2me | solution 1 for BanditAlgorithm.ucb_pull_count_bad_event_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-07-19T03:25:19.300828+00:00
-- url     : https://prove2.me/submissions/3a9102fc-43b0-40f3-b34d-4854971bccad

import Definitions.Def_ucbStoppedCenteredSum
import Definitions.Def_ucbPolicy
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy
import Mathlib.Data.Fintype.Order

/-!
Direct-proof work for Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020),
Theorem 7.1, printed pp. 105--108 (PDF pp. 114--117). The final theorem below
formalizes Eq. (7.5): a pull-count cap `u` on a measurable good event `G`, plus
the pathwise horizon cap `T_i(n) ≤ n`, gives
`E[T_i(n)] ≤ u + n P(Gᶜ)`.
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

end BanditAlgorithm


/-!
Direct work on the deterministic inclusion remaining in Lattimore--Szepesvári,
*Bandit Algorithms* (CUP 2020), Theorem 7.1, printed pp. 106--108
(PDF pp. 115--117), Eqs. (7.6)--(7.10). The stopped concentration bounds are
already available in the bot8 handoff. This file isolates the complementary
pathwise index contradiction: if UCB selects a suboptimal arm while both the
optimal-arm lower estimate and the suboptimal-arm upper estimate are good,
then the selected index would be simultaneously at least and strictly below
the optimal mean.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem measurable_armPullCount_cast_index_scratch {k m : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k m ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hset : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by ext t; simp
    rw [hset]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin m ↦ (h t).1 = i)
        Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k m ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

/-- Measurability of the empirical mean and UCB index, needed to transport
the one-step UCB rule through `Measure.map` in the remaining path-support
induction. -/
theorem measurable_armEmpiricalMean_index_scratch {k m : ℕ} (i : Fin k) :
    Measurable (armEmpiricalMean i : BanditHistory k m → ℝ) := by
  rw [show (armEmpiricalMean i : BanditHistory k m → ℝ) = fun h ↦
      (∑ t, if (h t).1 = i then (h t).2 else 0) / (armPullCount i h : ℝ) by
    funext h
    rw [armEmpiricalMean]
    have hset : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by ext t; simp
    rw [hset, Finset.sum_filter]]
  apply Measurable.div
  · apply Finset.measurable_sum
    intro t ht
    have harm : Measurable (fun h : BanditHistory k m ↦ (h t).1) :=
      measurable_fst.comp (measurable_pi_apply t)
    have hreward : Measurable (fun h : BanditHistory k m ↦ (h t).2) :=
      measurable_snd.comp (measurable_pi_apply t)
    exact Measurable.ite ((measurableSet_singleton i).preimage harm)
      hreward measurable_const
  · exact measurable_armPullCount_cast_index_scratch i

theorem measurable_ucbIndex_index_scratch {k m : ℕ} (δ : ℝ) (i : Fin k) :
    Measurable (ucbIndex δ i : BanditHistory k m → ℝ) := by
  rw [show (ucbIndex δ i : BanditHistory k m → ℝ) = fun h ↦
      armEmpiricalMean i h +
        Real.sqrt (2 * Real.log (1 / δ) / (armPullCount i h : ℝ)) by rfl]
  exact (measurable_armEmpiricalMean_index_scratch i).add
    (Real.continuous_sqrt.measurable.comp
      (measurable_const.div (measurable_armPullCount_cast_index_scratch i)))

theorem measurableSet_ucbRuleForArm_index_scratch
    {k m : ℕ} (δ : ℝ) (a : Fin k) :
    MeasurableSet {h : BanditHistory k m |
      ((∃ j, armPullCount j h = 0) → armPullCount a h = 0) ∧
      ((∀ j, armPullCount j h ≠ 0) →
        ∀ j, ucbIndex δ j h ≤ ucbIndex δ a h)} := by
  classical
  have hcount (j : Fin k) :
      Measurable (fun h : BanditHistory k m ↦ (armPullCount j h : ℝ)) :=
    measurable_armPullCount_cast_index_scratch j
  have hindex (j : Fin k) :
      Measurable (ucbIndex δ j : BanditHistory k m → ℝ) :=
    measurable_ucbIndex_index_scratch δ j
  have hz (j : Fin k) :
      MeasurableSet {h : BanditHistory k m | armPullCount j h = 0} := by
    simpa only [Nat.cast_eq_zero] using
      measurableSet_eq_fun (hcount j)
        (measurable_const : Measurable (fun _ : BanditHistory k m ↦ (0 : ℝ)))
  have hExists :
      MeasurableSet {h : BanditHistory k m | ∃ j, armPullCount j h = 0} := by
    convert MeasurableSet.iUnion (fun j : Fin k ↦ hz j) using 1
    ext h
    simp
  have hAllIndex : MeasurableSet {h : BanditHistory k m |
      ∀ j, ucbIndex δ j h ≤ ucbIndex δ a h} := by
    convert MeasurableSet.iInter (fun j : Fin k ↦
      measurableSet_le (hindex j) (hindex a)) using 1
    ext h
    simp
  convert (hExists.compl.union (hz a)).inter (hExists.union hAllIndex) using 1
  ext h
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  by_cases hex : ∃ j, armPullCount j h = 0
  · obtain ⟨j, hj⟩ := hex
    constructor
    · intro hl
      exact ⟨Or.inr (hl.1 ⟨j, hj⟩), Or.inl ⟨j, hj⟩⟩
    · intro hr
      constructor
      · intro _
        rcases hr.1 with hnot | ha
        · exact False.elim (hnot ⟨j, hj⟩)
        · exact ha
      · intro hall
        exact False.elim ((hall j) hj)
  · have hall : ∀ j, armPullCount j h ≠ 0 := by
      intro j hj
      exact hex ⟨j, hj⟩
    constructor
    · intro hl
      exact ⟨Or.inl hex, Or.inr (hl.2 hall)⟩
    · intro hr
      constructor
      · intro he
        exact False.elim (hex he)
      · intro _
        rcases hr.2 with he | hi
        · exact False.elim (hex he)
        · exact hi

/-- The last observed arm of a nonempty history obeys the UCB selection rule
at the preceding prefix. -/
def LastStepObeysUCB {k m : ℕ} (δ : ℝ) (h : BanditHistory k (m + 1)) : Prop :=
  ((∃ j, armPullCount j (Fin.init h) = 0) →
      armPullCount (h (Fin.last m)).1 (Fin.init h) = 0) ∧
  ((∀ j, armPullCount j (Fin.init h) ≠ 0) →
      ∀ j, ucbIndex δ j (Fin.init h) ≤
        ucbIndex δ (h (Fin.last m)).1 (Fin.init h))

theorem measurableSet_lastStepObeysUCB_index_scratch
    {k m : ℕ} (δ : ℝ) :
    MeasurableSet {h : BanditHistory k (m + 1) | LastStepObeysUCB δ h} := by
  classical
  have hlast : Measurable
      (fun h : BanditHistory k (m + 1) ↦ (h (Fin.last m)).1) :=
    measurable_fst.comp (measurable_pi_apply (Fin.last m))
  have hinit : Measurable
      (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
    fun_prop
  have hpiece (a : Fin k) : MeasurableSet
      ({h : BanditHistory k (m + 1) | (h (Fin.last m)).1 = a} ∩
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) ⁻¹'
          {q : BanditHistory k m |
            ((∃ j, armPullCount j q = 0) → armPullCount a q = 0) ∧
            ((∀ j, armPullCount j q ≠ 0) →
              ∀ j, ucbIndex δ j q ≤ ucbIndex δ a q)}) := by
    exact (measurableSet_eq_fun hlast measurable_const).inter
      ((measurableSet_ucbRuleForArm_index_scratch δ a).preimage hinit)
  convert MeasurableSet.iUnion (fun a : Fin k ↦ hpiece a) using 1
  ext h
  simp [LastStepObeysUCB]

/-- Almost-sure one-step path-support theorem. This is the measure-theoretic
transport needed to turn the deterministic index alternative into an event
inclusion on canonical histories. -/
theorem banditMeasure_ae_lastStepObeysUCB_index_scratch
    {k m : ℕ} (ν : StochasticBandit k) {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) :
    ∀ᵐ h ∂banditMeasure ν π (m + 1), LastStepObeysUCB δ h := by
  have hset := measurableSet_lastStepObeysUCB_index_scratch
    (k := k) (m := m) δ
  rw [banditMeasure]
  rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
  apply Measure.ae_compProd_of_ae_ae
  · exact measurable_banditHistorySnoc hset
  · filter_upwards [] with h
    simpa [LastStepObeysUCB] using
      banditStepKernel_ae_obeys_ucb_rule ν hπ h

/-- Recursive all-prefix version of `LastStepObeysUCB`. -/
def HistoryObeysUCB {k : ℕ} (δ : ℝ) :
    {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => True
  | m + 1, h => HistoryObeysUCB δ (Fin.init h) ∧ LastStepObeysUCB δ h

theorem measurableSet_historyObeysUCB_index_scratch
    {k : ℕ} (δ : ℝ) : ∀ m : ℕ,
    MeasurableSet {h : BanditHistory k m | HistoryObeysUCB δ h} := by
  intro m
  induction m with
  | zero => simp [HistoryObeysUCB]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        fun_prop
      change MeasurableSet
        ({h : BanditHistory k (m + 1) | HistoryObeysUCB δ (Fin.init h)} ∩
          {h : BanditHistory k (m + 1) | LastStepObeysUCB δ h})
      exact (ih.preimage hinit).inter
        (measurableSet_lastStepObeysUCB_index_scratch δ)

/-- Canonical histories generated by a UCB policy obey the UCB selection rule
at every prefix, almost surely. -/
theorem banditMeasure_ae_historyObeysUCB_index_scratch
    {k : ℕ} (ν : StochasticBandit k) {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) : ∀ m : ℕ,
    ∀ᵐ h ∂banditMeasure ν π m, HistoryObeysUCB δ h := by
  intro m
  induction m with
  | zero => simp [banditMeasure, HistoryObeysUCB]
  | succ m ih =>
      have hset := measurableSet_historyObeysUCB_index_scratch
        (k := k) δ (m + 1)
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih] with h hh
        filter_upwards [banditStepKernel_ae_obeys_ucb_rule ν hπ h] with z hz
        rw [HistoryObeysUCB, LastStepObeysUCB]
        simp only [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hh, hz⟩

/-- Recursive path predicate saying that at some round the arm `i` is selected
immediately after a prefix on which it has been pulled exactly `u` times. Its
recursive shape matches the `Fin.init`/last-round construction of
`banditMeasure`. -/
def HasArmPullAfterCount {k : ℕ} (i : Fin k) (u : ℕ) :
    {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => False
  | m + 1, h =>
      HasArmPullAfterCount i u (Fin.init h) ∨
        (armPullCount i (Fin.init h) = u ∧ (h (Fin.last m)).1 = i)

/-- Finite-history counting bridge: if the final pull count exceeds `u`, then
the history contains the `(u+1)`st pull, represented by a prefix with count
exactly `u` followed by selection of `i`. -/
theorem hasArmPullAfterCount_of_lt_pullCount
    {k m : ℕ} (i : Fin k) (u : ℕ) (h : BanditHistory k m)
    (hu : u < armPullCount i h) : HasArmPullAfterCount i u h := by
  induction m with
  | zero => simp [armPullCount] at hu
  | succ m ih =>
      rw [← Fin.snoc_init_self h] at hu ⊢
      rw [armPullCount_snoc] at hu
      simp only [HasArmPullAfterCount, Fin.init_snoc, Fin.snoc_last]
      by_cases hprev : u < armPullCount i (Fin.init h)
      · exact Or.inl (ih (Fin.init h) hprev)
      · right
        have hprev_le : armPullCount i (Fin.init h) ≤ u := Nat.le_of_not_gt hprev
        by_cases hlast : (h (Fin.last m)).1 = i
        · simp [hlast] at hu
          exact ⟨by omega, hlast⟩
        · simp [hlast] at hu
          omega

/-- Recursive witness of an `(u+1)`st pull at which the selected suboptimal
arm's UCB index dominates a comparison arm. -/
def HasDominatingArmPullAfterCount {k : ℕ} (δ : ℝ)
    (i j : Fin k) (u : ℕ) : {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => False
  | m + 1, h =>
      HasDominatingArmPullAfterCount δ i j u (Fin.init h) ∨
        (armPullCount i (Fin.init h) = u ∧
          (h (Fin.last m)).1 = i ∧
          ucbIndex δ j (Fin.init h) ≤ ucbIndex δ i (Fin.init h))

theorem hasDominatingArmPullAfterCount_of_obeys
    {k m : ℕ} {δ : ℝ} (i j : Fin k) {u : ℕ} (hu : u ≠ 0)
    (h : BanditHistory k m) (hobeys : HistoryObeysUCB δ h)
    (hpull : HasArmPullAfterCount i u h) :
    HasDominatingArmPullAfterCount δ i j u h := by
  induction m with
  | zero => simp [HasArmPullAfterCount] at hpull
  | succ m ih =>
      rw [HistoryObeysUCB] at hobeys
      rw [HasArmPullAfterCount] at hpull
      rw [HasDominatingArmPullAfterCount]
      rcases hobeys with ⟨hobeys, hlastRule⟩
      rcases hpull with hpull | hpull
      · exact Or.inl (ih (Fin.init h) hobeys hpull)
      · right
        have hcount_ne : armPullCount (h (Fin.last m)).1 (Fin.init h) ≠ 0 := by
          simpa [hpull.2, hpull.1] using hu
        have hall : ∀ a, armPullCount a (Fin.init h) ≠ 0 := by
          by_contra hnot
          push Not at hnot
          exact hcount_ne (hlastRule.1 hnot)
        exact ⟨hpull.1, hpull.2, by simpa [hpull.2] using hlastRule.2 hall j⟩

/-- Recursive support predicate for histories whose observed arms agree with
the deterministic selections made by a policy at every prefix. Proving this
predicate almost surely for `banditMeasure` is the remaining measure-support
transport step after the present deterministic work. -/
def HistoryFollowsDeterministicPolicy {k : ℕ} (π : BanditPolicy k) :
    {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => True
  | m + 1, h =>
      HistoryFollowsDeterministicPolicy π (Fin.init h) ∧
        (π.select m) (Fin.init h) = Measure.dirac (h (Fin.last m)).1

/-- Recursive witness that a policy-following history contains the `(u+1)`st
pull of arm `i`, including the exact prefix and the policy's Dirac selection
at that round. -/
def HasPolicyArmPullAfterCount {k : ℕ} (π : BanditPolicy k)
    (i : Fin k) (u : ℕ) : {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => False
  | m + 1, h =>
      HasPolicyArmPullAfterCount π i u (Fin.init h) ∨
        (armPullCount i (Fin.init h) = u ∧
          (h (Fin.last m)).1 = i ∧
          (π.select m) (Fin.init h) = Measure.dirac i)

theorem hasPolicyArmPullAfterCount_of_follows
    {k m : ℕ} (π : BanditPolicy k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m)
    (hfollows : HistoryFollowsDeterministicPolicy π h)
    (hpull : HasArmPullAfterCount i u h) :
    HasPolicyArmPullAfterCount π i u h := by
  induction m with
  | zero => simp [HasArmPullAfterCount] at hpull
  | succ m ih =>
      rw [HistoryFollowsDeterministicPolicy] at hfollows
      rw [HasArmPullAfterCount] at hpull
      rw [HasPolicyArmPullAfterCount]
      rcases hfollows with ⟨hfollows, hselect⟩
      rcases hpull with hpull | hpull
      · exact Or.inl (ih (Fin.init h) hfollows hpull)
      · right
        refine ⟨hpull.1, hpull.2, ?_⟩
        simpa [hpull.2] using hselect

theorem IsUCBPolicy.selected_index_dominates_minimax_scratch
    {k : ℕ} {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m) (i j : Fin k)
    (hselect : (π.select m) h = Measure.dirac i)
    (hall : ∀ a, armPullCount a h ≠ 0) :
    ucbIndex δ j h ≤ ucbIndex δ i h := by
  obtain ⟨a, hdirac, _, hmax⟩ := hπ m h
  have hai : a = i := dirac_eq_dirac_iff.mp (hdirac.symm.trans hselect)
  simpa [hai] using hmax hall j

/-- After UCB selects an arm that was already pulled, initialization is over:
every arm has nonzero pull count. This discharges the hypothesis needed to
invoke index maximality at the `(u+1)`st pull when `u > 0`. -/
theorem IsUCBPolicy.all_pulled_of_selects_previously_pulled
    {k : ℕ} {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) {m : ℕ} (h : BanditHistory k m) (i : Fin k)
    (hselect : (π.select m) h = Measure.dirac i)
    (hi : armPullCount i h ≠ 0) :
    ∀ j, armPullCount j h ≠ 0 := by
  intro j hj
  obtain ⟨a, hdirac, hunpulled, _⟩ := hπ m h
  have hai : a = i := dirac_eq_dirac_iff.mp (hdirac.symm.trans hselect)
  have ha0 := hunpulled ⟨j, hj⟩
  exact hi (by simpa [hai] using ha0)

/-- The pointwise algebra at the heart of the bad-event inclusion in the proof
of Theorem 7.1. The optimal arm's good lower confidence estimate makes its UCB
index strictly larger than its mean; the suboptimal arm's good upper estimate
and radius bound make its UCB index at most that same optimal mean. Hence UCB
cannot select the suboptimal arm. -/
theorem ucb_selected_suboptimal_forces_bad_estimate
    {k m : ℕ} (ν : StochasticBandit k) (δ : ℝ)
    (h : BanditHistory k m) (i j : Fin k)
    (hjopt : banditGap ν j = 0)
    (hindex : ucbIndex δ j h ≤ ucbIndex δ i h)
    (hjgood : banditArmMean ν j <
      armEmpiricalMean j h +
        Real.sqrt (2 * Real.log (1 / δ) / armPullCount j h))
    (higood : armEmpiricalMean i h - banditArmMean ν i < banditGap ν i / 2)
    (hiradius :
      Real.sqrt (2 * Real.log (1 / δ) / armPullCount i h) ≤
        banditGap ν i / 2) : False := by
  have hjmean : banditOptimalMean ν = banditArmMean ν j := by
    rw [banditGap] at hjopt
    linarith
  have hgap : banditGap ν i = banditArmMean ν j - banditArmMean ν i := by
    rw [banditGap, hjmean]
  simp only [ucbIndex] at hindex
  nlinarith

/-- The numerical radius estimate used with Eq. (7.8), specialized to the
source's choices `δ = 1/n²`, `c = 1/2`, and
`u = ceil (16 log n / gap²)`. Once an arm already has at least `u` samples,
its UCB confidence radius is at most half its gap. -/
theorem ucb_radius_le_half_gap_of_pull_cap
    {n : ℕ} (hn : 1 < n) {gap : ℝ} (hgap : 0 < gap) {s : ℕ}
    (hcap : ⌈16 * Real.log n / gap ^ 2⌉₊ ≤ s) :
    Real.sqrt (2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) / s) ≤ gap / 2 := by
  have hnR : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hgap_sq : 0 < gap ^ 2 := sq_pos_of_pos hgap
  have hceil_pos : 0 < ⌈16 * Real.log n / gap ^ 2⌉₊ := by
    rw [Nat.ceil_pos]
    exact div_pos (mul_pos (by norm_num) hlog) hgap_sq
  have hs : 0 < s := hceil_pos.trans_le hcap
  have hu : 16 * Real.log n / gap ^ 2 ≤ (s : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hcap)
  have hmul : 16 * Real.log n ≤ (s : ℝ) * gap ^ 2 :=
    (div_le_iff₀ hgap_sq).mp hu
  have hlog_delta :
      2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) = 4 * Real.log n := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    rw [one_div_div, div_one, Real.log_pow]
    ring
  have harg : 0 ≤ 2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) / (s : ℝ) := by
    rw [hlog_delta]
    positivity
  have hfrac :
      2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) / (s : ℝ) ≤ gap ^ 2 / 4 := by
    rw [hlog_delta]
    apply (div_le_iff₀ (by exact_mod_cast hs)).2
    nlinarith
  have hsqrt_sq := Real.sq_sqrt harg
  have hsqrt_nonneg := Real.sqrt_nonneg
    (2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) / (s : ℝ))
  nlinarith [sq_nonneg
    (Real.sqrt (2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) / (s : ℝ)) - gap / 2)]

/-- Packaged one-step event inclusion: once all arms have been initialized and
the selected suboptimal arm's radius is below half its gap, selecting that arm
forces either the optimal lower-confidence estimate or the suboptimal
upper-confidence estimate to fail. This is the deterministic alternative in
Eqs. (7.6)--(7.8). -/
theorem ucb_selected_suboptimal_implies_confidence_failure
    {k m : ℕ} (ν : StochasticBandit k) {δ : ℝ} {π : BanditPolicy k}
    (hπ : IsUCBPolicy δ π) (h : BanditHistory k m) (i j : Fin k)
    (hselect : (π.select m) h = Measure.dirac i)
    (hall : ∀ a, armPullCount a h ≠ 0)
    (hjopt : banditGap ν j = 0)
    (hiradius :
      Real.sqrt (2 * Real.log (1 / δ) / armPullCount i h) ≤
        banditGap ν i / 2) :
    ¬(banditArmMean ν j <
        armEmpiricalMean j h +
          Real.sqrt (2 * Real.log (1 / δ) / armPullCount j h)) ∨
      ¬(armEmpiricalMean i h - banditArmMean ν i < banditGap ν i / 2) := by
  by_contra hgood
  push Not at hgood
  exact ucb_selected_suboptimal_forces_bad_estimate ν δ h i j hjopt
    (hπ.selected_index_dominates_minimax_scratch h i j hselect hall)
    hgood.1 hgood.2 hiradius

end BanditAlgorithm

/-!
Direct continuation for Lattimore--Szepesvári, *Bandit Algorithms* (CUP
2020), Theorem 7.1, printed pp. 105--107 (PDF pp. 114--116), specifically the
crossing-time UCB contradiction preceding Eq. (7.6) and the stopped empirical
events in Eqs. (7.6)--(7.8).  The lemmas below connect a canonical history's
`(u+1)`st pull to the stopped sums used by the platform leaf.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private noncomputable def armCenteredHistorySum {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k m) : ℝ :=
  ∑ t ∈ {t | (h t).1 = i}.toFinset, ((h t).2 - banditArmMean ν i)

private theorem armCenteredHistorySum_snoc {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k m)
    (z : Fin k × ℝ) :
    armCenteredHistorySum ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredHistorySum ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  classical
  simp only [armCenteredHistorySum]
  rw [show {t | ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦
        ((Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) t).1 = i) by ext t; simp]
  rw [show {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) by ext t; simp]
  simp only [Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armStoppedCenteredSum_eq_historySum_of_count_le
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hle : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h = armCenteredHistorySum ν i h := by
  induction m with
  | zero => simp [armStoppedCenteredSum, armCenteredHistorySum]
  | succ m ih =>
      rw [← Fin.snoc_init_self h] at hle ⊢
      rw [armPullCount_snoc] at hle
      rw [armCenteredHistorySum_snoc]
      simp only [armStoppedCenteredSum, Fin.init_snoc, Fin.snoc_last]
      by_cases hz : (h (Fin.last m)).1 = i
      · have hprev : armPullCount i (Fin.init h) < u := by
          simp [hz] at hle
          omega
        rw [if_pos ⟨hprev, hz⟩, if_pos hz,
          ih (Fin.init h) (Nat.le_of_lt hprev)]
      · rw [if_neg (fun hcond ↦ hz hcond.2), if_neg hz,
          ih (Fin.init h) (by simpa [hz] using hle)]

private theorem armCenteredHistorySum_eq_count_mul_empiricalMean_sub
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k m) :
    armCenteredHistorySum ν i h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  classical
  rw [armCenteredHistorySum, armEmpiricalMean]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  by_cases hc : armPullCount i h = 0
  · have hempty : {t | (h t).1 = i}.toFinset = ∅ := by
      rw [armPullCount] at hc
      exact Finset.card_eq_zero.mp hc
    simp [hc, hempty]
  · have hcard : (({t | (h t).1 = i}.toFinset.card : ℕ) : ℝ) =
        (armPullCount i h : ℝ) := by rfl
    rw [hcard]
    field_simp
    <;> ring

theorem armStoppedCenteredSum_eq_count_mul_empiricalMean_sub
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hle : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  rw [armStoppedCenteredSum_eq_historySum_of_count_le ν i u h hle,
    armCenteredHistorySum_eq_count_mul_empiricalMean_sub]

theorem armStoppedCenteredSum_snoc_of_cap_reached
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ)
    (hcap : u ≤ armPullCount i h) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h := by
  rw [armStoppedCenteredSum.eq_def]
  simp [Nat.not_lt_of_ge hcap]

/-- A strengthened stopped-event disjunction.  Besides the two inequalities it
records that each stopping cap has already been reached, which makes the
property stable under extending a history. -/
def UCBStoppedBadWitness {k n m : ℕ} (ν : StochasticBandit k)
    (i j : Fin k) (u : ℕ) (h : BanditHistory k m) : Prop :=
  (∃ s : ℕ, 0 < s ∧ s ≤ armPullCount j h ∧
    armStoppedCenteredSum ν j s m h ≤
      -(s : ℝ) * Real.sqrt
        (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))) ∨
  (u ≤ armPullCount i h ∧
    (u : ℝ) * (banditGap ν i / 2) ≤
      armStoppedCenteredSum ν i u m h)

theorem UCBStoppedBadWitness.snoc {k n m : ℕ} (ν : StochasticBandit k)
    (i j : Fin k) (u : ℕ) (h : BanditHistory k m)
    (z : Fin k × ℝ) (hbad : UCBStoppedBadWitness (n := n) ν i j u h) :
    UCBStoppedBadWitness (n := n) ν i j u
      (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) := by
  rcases hbad with hopt | hsub
  · left
    obtain ⟨s, hs, hscount, hsbad⟩ := hopt
    refine ⟨s, hs, ?_, ?_⟩
    · rw [armPullCount_snoc]
      omega
    · rw [armStoppedCenteredSum_snoc_of_cap_reached ν j s h z hscount]
      exact hsbad
  · right
    refine ⟨?_, ?_⟩
    · rw [armPullCount_snoc]
      omega
    · rw [armStoppedCenteredSum_snoc_of_cap_reached ν i u h z hsub.1]
      exact hsub.2

theorem ucb_pull_cap_pos {n : ℕ} (hn : 1 < n) {gap : ℝ}
    (hgap : 0 < gap) : 0 < ⌈16 * Real.log n / gap ^ 2⌉₊ := by
  rw [Nat.ceil_pos]
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn)))
    (sq_pos_of_pos hgap)

/-- At the exact `(u+1)`st pull, maximality of the selected UCB index forces
one of the source's two stopped confidence failures. -/
theorem ucb_crossing_forces_stopped_bad
    {k n m : ℕ} (hn : 1 < n) (ν : StochasticBandit k)
    (i j : Fin k) (hi : 0 < banditGap ν i) (hjopt : banditGap ν j = 0)
    (h : BanditHistory k m)
    (hiCount : armPullCount i h =
      ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊)
    (hall : ∀ a, armPullCount a h ≠ 0)
    (hindex :
      ucbIndex (1 / (n : ℝ) ^ 2) j h ≤
        ucbIndex (1 / (n : ℝ) ^ 2) i h) :
    UCBStoppedBadWitness (n := n) ν i j
      ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ h := by
  let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
  let s : ℕ := armPullCount j h
  have hu : 0 < u := ucb_pull_cap_pos hn hi
  have hs : 0 < s := Nat.pos_of_ne_zero (hall j)
  have hiCount' : armPullCount i h = u := hiCount
  have hstopi : armStoppedCenteredSum ν i u m h =
      (u : ℝ) * (armEmpiricalMean i h - banditArmMean ν i) := by
    rw [armStoppedCenteredSum_eq_count_mul_empiricalMean_sub ν i u h (by omega),
      hiCount']
  have hstopj : armStoppedCenteredSum ν j s m h =
      (s : ℝ) * (armEmpiricalMean j h - banditArmMean ν j) := by
    apply armStoppedCenteredSum_eq_count_mul_empiricalMean_sub
    exact le_rfl
  by_cases hopt : armStoppedCenteredSum ν j s m h ≤
      -(s : ℝ) * Real.sqrt
        (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
  · exact Or.inl ⟨s, hs, le_rfl, hopt⟩
  by_cases hsub : (u : ℝ) * (banditGap ν i / 2) ≤
      armStoppedCenteredSum ν i u m h
  · exact Or.inr ⟨by omega, hsub⟩
  exfalso
  have hdelta : 1 / (1 / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hjgood : banditArmMean ν j < armEmpiricalMean j h +
      Real.sqrt
        (2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) /
          armPullCount j h) := by
    rw [hdelta]
    change banditArmMean ν j < armEmpiricalMean j h +
      Real.sqrt (2 * Real.log ((n : ℝ) ^ 2) / (s : ℝ))
    push Not at hopt
    nlinarith
  have higood : armEmpiricalMean i h - banditArmMean ν i <
      banditGap ν i / 2 := by
    push Not at hsub
    nlinarith
  have hiradius :
      Real.sqrt
          (2 * Real.log (1 / (1 / (n : ℝ) ^ 2)) /
            armPullCount i h) ≤
        banditGap ν i / 2 := by
    rw [hiCount']
    exact ucb_radius_le_half_gap_of_pull_cap hn hi le_rfl
  exact ucb_selected_suboptimal_forces_bad_estimate ν
    (1 / (n : ℝ) ^ 2) h i j hjopt hindex hjgood higood hiradius

/-- Combining the all-prefix UCB support theorem with the finite-history
crossing witness yields a stopped bad-event witness on the final history. -/
theorem ucbStoppedBadWitness_of_obeys_of_lt_pullCount
    {k n m : ℕ} (hn : 1 < n) (ν : StochasticBandit k)
    (i j : Fin k) (hi : 0 < banditGap ν i) (hjopt : banditGap ν j = 0)
    (h : BanditHistory k m)
    (hobeys : HistoryObeysUCB (1 / (n : ℝ) ^ 2) h)
    (hpull : HasArmPullAfterCount i
      ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ h) :
    UCBStoppedBadWitness (n := n) ν i j
      ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊ h := by
  induction m with
  | zero => simp [HasArmPullAfterCount] at hpull
  | succ m ih =>
      rw [HistoryObeysUCB] at hobeys
      rw [HasArmPullAfterCount] at hpull
      rcases hobeys with ⟨hobeys, hlastRule⟩
      rcases hpull with hpull | hpull
      · rw [← Fin.snoc_init_self h]
        exact UCBStoppedBadWitness.snoc (n := n) ν i j _ _
          (h (Fin.last m)) (ih (Fin.init h) hobeys hpull)
      · let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
        have hu : u ≠ 0 := Nat.ne_of_gt (ucb_pull_cap_pos hn hi)
        have hselected_ne :
            armPullCount (h (Fin.last m)).1 (Fin.init h) ≠ 0 := by
          rw [hpull.2, hpull.1]
          exact hu
        have hall : ∀ a, armPullCount a (Fin.init h) ≠ 0 := by
          intro a ha
          exact hselected_ne (hlastRule.1 ⟨a, ha⟩)
        have hindex :
            ucbIndex (1 / (n : ℝ) ^ 2) j (Fin.init h) ≤
              ucbIndex (1 / (n : ℝ) ^ 2) i (Fin.init h) := by
          simpa [hpull.2] using hlastRule.2 hall j
        have hbad := ucb_crossing_forces_stopped_bad hn ν i j hi hjopt
          (Fin.init h) hpull.1 hall hindex
        rw [← Fin.snoc_init_self h]
        exact UCBStoppedBadWitness.snoc (n := n) ν i j _ _
          (h (Fin.last m)) hbad

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    {n : ℕ} (hn : 0 < n) (hkn : k < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    ∃ j : Fin k, banditArmMean ν j = banditOptimalMean ν ∧
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
        u < armPullCount i h → h ∈ ((⋃ r, optBad r) ∪ subBad) := by
  have hn2 : 1 < n := by omega
  obtain ⟨j, hjopt⟩ := exists_optimal_arm hk ν
  have hjmean : banditArmMean ν j = banditOptimalMean ν := by
    rw [banditGap] at hjopt
    linarith
  refine ⟨j, hjmean, ?_⟩
  dsimp only
  filter_upwards
      [banditMeasure_ae_historyObeysUCB_index_scratch ν hπ n] with h hobeys
  intro hpull
  let u : ℕ := ⌈16 * Real.log n / (banditGap ν i) ^ 2⌉₊
  have hcross : HasArmPullAfterCount i u h :=
    hasArmPullAfterCount_of_lt_pullCount i u h hpull
  have hbad : UCBStoppedBadWitness (n := n) ν i j u h :=
    ucbStoppedBadWitness_of_obeys_of_lt_pullCount hn2 ν i j hi hjopt h
      hobeys hcross
  rcases hbad with hopt | hsub
  · left
    obtain ⟨s, hs, hscount, hsbad⟩ := hopt
    have hsn : s ≤ n := hscount.trans (armPullCount_le_horizon j h)
    let r : Fin n := ⟨s - 1, by omega⟩
    refine Set.mem_iUnion.mpr ⟨r, ?_⟩
    change armStoppedCenteredSum ν j (r + 1) n h ≤
      -((r + 1 : ℕ) : ℝ) * Real.sqrt
        (2 * Real.log ((n : ℝ) ^ 2) / ((r + 1 : ℕ) : ℝ))
    have hrs : r + 1 = s := by
      change (s - 1 : ℕ) + 1 = s
      omega
    simpa [hrs] using hsbad
  · right
    exact hsub.2
