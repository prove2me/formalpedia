-- Prove2me | solution 1 for BanditAlgorithm.bandit_kl_ucb_feasibility_pull_count_split
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T04:22:39.087002+00:00
-- url     : https://prove2.me/submissions/e41a7b0a-d142-49a9-bc72-b1d64cea5b8e

import Definitions.Def_klucbFeasibilityFailureCount
import Theorems.Thm_BanditAlgorithm_klucb_index_threshold_feasible
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

/-!
Direct formalization of the pathwise split in Lattimore--Szepesvári,
*Bandit Algorithms* (CUP 2020), Theorem 10.6, proof on p. 139, printed p. 119 /
PDF p. 128.  The canonical kernel law is first shown to support histories
which obey Algorithm 8 at every prefix; the finite-history counting argument
then charges every pull after the first to one of the two index failures.
-/

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator_split {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hs : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hs]
  simpa using
    (Finset.sum_boole (R := ℝ)
      (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

private theorem measurable_armPullCount_split {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  simp_rw [pullCount_cast_eq_sum_indicator_split]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite
    ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

private theorem integrable_armPullCount_split {k n : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_armPullCount_split i).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · rw [pullCount_cast_eq_sum_indicator_split]
        calc
          (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
              ∑ _t : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro t ht
            split <;> norm_num
          _ = n := by simp

private theorem armPullCount_snoc_split {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, pullCount_cast_eq_sum_indicator_split,
    pullCount_cast_eq_sum_indicator_split i h, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem banditStepKernel_ae_selected_arm_split
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.1 = a := by
  let μ := banditStepKernel ν π m h
  have hfst : Measure.map Prod.fst μ = Measure.dirac a := by
    rw [← Kernel.fst_apply, banditStepKernel, Kernel.fst_compProd]
    exact hselect
  have hmap : ∀ᵐ b ∂Measure.map Prod.fst μ, b = a := by
    rw [hfst]
    simp
  exact
    (ae_map_iff (μ := μ) measurable_fst.aemeasurable
      (by measurability)).1 hmap

private theorem measurable_armEmpiricalMean_split {k m : ℕ} (i : Fin k) :
    Measurable (armEmpiricalMean (n := m) i) := by
  have hsum :
      (fun h : BanditHistory k m ↦
        ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) =
      fun h ↦ ∑ t, if (h t).1 = i then (h t).2 else 0 := by
    funext h
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs, Finset.sum_filter]
  have hnum : Measurable
      (fun h : BanditHistory k m ↦
        ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) := by
    rw [hsum]
    apply Finset.measurable_sum
    intro t ht
    have ha : Measurable (fun h : BanditHistory k m ↦ (h t).1) :=
      measurable_fst.comp (measurable_pi_apply t)
    have hx : Measurable (fun h : BanditHistory k m ↦ (h t).2) :=
      measurable_snd.comp (measurable_pi_apply t)
    exact Measurable.ite ((measurableSet_singleton i).preimage ha)
      hx measurable_const
  unfold armEmpiricalMean
  exact hnum.div (measurable_armPullCount_split i)

private def HistoryRewardsBernoulli {k n : ℕ}
    (h : BanditHistory k n) : Prop :=
  ∀ t, (h t).2 = 0 ∨ (h t).2 = 1

private theorem empiricalMean_mem_Icc_of_rewardsBernoulli
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (hh : HistoryRewardsBernoulli h) :
    armEmpiricalMean i h ∈ Set.Icc (0 : ℝ) 1 := by
  let S : Finset (Fin n) := {t | (h t).1 = i}.toFinset
  have hreward (t : Fin n) : 0 ≤ (h t).2 ∧ (h t).2 ≤ 1 := by
    rcases hh t with ht | ht <;> simp [ht]
  have hnum0 : 0 ≤ ∑ t ∈ S, (h t).2 :=
    Finset.sum_nonneg fun t _ ↦ (hreward t).1
  have hnumle : (∑ t ∈ S, (h t).2) ≤ (S.card : ℝ) := by
    calc
      (∑ t ∈ S, (h t).2) ≤ ∑ _t ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ ↦ (hreward t).2
      _ = (S.card : ℝ) := by simp
  unfold armEmpiricalMean
  change (∑ t ∈ S, (h t).2) / (S.card : ℝ) ∈ Set.Icc (0 : ℝ) 1
  by_cases hc : S.card = 0
  · simp [hc]
  · have hcpos : 0 < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
    exact ⟨div_nonneg hnum0 hcpos.le,
      (div_le_one hcpos).2 hnumle⟩

private theorem banditArmMean_bernoulli_split
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (i : Fin k) :
    banditArmMean ν i = μvec i := by
  rw [hν, banditArmMean, bernoulliBandit]
  change (∫ x : ℝ, x ∂(ENNReal.ofReal (μvec i) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - μvec i) • Measure.dirac (0 : ℝ))) = μvec i
  rw [integral_add_measure
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (1 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)]
  rcases hμ i with ⟨h0, h1⟩
  simp [ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - μvec i by linarith)]

private theorem one_le_klucbExploration_split (t : ℕ) :
    1 ≤ klucbExploration t := by
  rw [klucbExploration]
  exact le_add_of_nonneg_right
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

private def FeasibilityDichotomy {k m : ℕ}
    (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) : Prop :=
  z.1 = i →
    ((¬ ∀ j, armPullCount j h ≠ 0) ∨
      Real.log (klucbExploration (m + 1)) / armPullCount a h <
        klucbTruncatedRelativeEntropy (armEmpiricalMean a h)
          (banditOptimalMean ν - ε)) ∨
    ((∀ j, armPullCount j h ≠ 0) ∧
      klucbTruncatedRelativeEntropy (armEmpiricalMean i h)
          (banditOptimalMean ν - ε) ≤
        Real.log (klucbExploration (m + 1)) / armPullCount i h)

private theorem selected_arm_feasibility_dichotomy_split
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π)
    (a i : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) (hεgap : ε < banditGap ν i)
    (h : BanditHistory k m) (hh : HistoryRewardsBernoulli h) :
    ∀ᵐ z ∂banditStepKernel ν π m h,
      FeasibilityDichotomy ν a i ε h z := by
  have hq : banditOptimalMean ν - ε ∈ Set.Ioo (0 : ℝ) 1 := by
    have hma : banditArmMean ν a ∈ Set.Icc (0 : ℝ) 1 := by
      rw [banditArmMean_bernoulli_split μvec hμ ν hν a]
      exact hμ a
    have hmi : 0 ≤ banditArmMean ν i := by
      rw [banditArmMean_bernoulli_split μvec hμ ν hν i]
      exact (hμ i).1
    rw [banditGap] at hεgap
    constructor
    · rw [← ha]
      linarith
    · rw [← ha]
      have hma1 := hma.2
      linarith
  have hpa :
      armEmpiricalMean a h ∈ Set.Icc (0 : ℝ) 1 :=
    empiricalMean_mem_Icc_of_rewardsBernoulli a h hh
  have hpi :
      armEmpiricalMean i h ∈ Set.Icc (0 : ℝ) 1 :=
    empiricalMean_mem_Icc_of_rewardsBernoulli i h hh
  obtain ⟨s, hsdirac, hsunpulled, hsmax⟩ := hπ m h
  have hsatisfies : FeasibilityDichotomy ν a i ε h (s, 0) := by
    intro hsi
    have hsi' : s = i := by simpa using hsi
    by_cases hall : ∀ j, armPullCount j h ≠ 0
    · by_cases hlow :
          Real.log (klucbExploration (m + 1)) / armPullCount a h <
            klucbTruncatedRelativeEntropy (armEmpiricalMean a h)
              (banditOptimalMean ν - ε)
      · exact Or.inl (Or.inr hlow)
      · right
        refine ⟨hall, ?_⟩
        have hqa :
            banditOptimalMean ν - ε ≤ klucbIndex a h := by
          apply
            (klucb_index_threshold_feasible a h
              (banditOptimalMean ν - ε) hq hpa).2
          exact le_of_not_gt hlow
        have hqs :
            banditOptimalMean ν - ε ≤ klucbIndex s h :=
          hqa.trans (hsmax hall a)
        have hqi :
            banditOptimalMean ν - ε ≤ klucbIndex i h := by
          simpa [hsi'] using hqs
        exact
          (klucb_index_threshold_feasible i h
            (banditOptimalMean ν - ε) hq hpi).1 hqi
    · exact Or.inl (Or.inl hall)
  filter_upwards
    [banditStepKernel_ae_selected_arm_split ν π h s hsdirac] with z hz
  intro hzi
  apply hsatisfies
  simpa [hz] using hzi

private theorem bernoulli_arm_ae_reward_split
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (j : Fin k) :
    ∀ᵐ x ∂ν.P j, x = 0 ∨ x = 1 := by
  rw [hν, bernoulliBandit]
  change ∀ᵐ x ∂(ENNReal.ofReal (μvec j) • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - μvec j) • Measure.dirac (0 : ℝ)),
    x = 0 ∨ x = 1
  rw [MeasureTheory.ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact Measure.ae_smul_measure (by simp) _

private theorem banditStepKernel_ae_reward_bernoulli_split
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.2 = 0 ∨ z.2 = 1 := by
  rw [banditStepKernel]
  apply Kernel.ae_compProd_of_ae_ae
  · exact (measurableSet_eq_fun measurable_snd measurable_const).union
      (measurableSet_eq_fun measurable_snd measurable_const)
  · filter_upwards with j
    rw [Kernel.comap_apply]
    exact bernoulli_arm_ae_reward_split μvec hμ ν hν j

private theorem measurableSet_initialized_split
    {k m : ℕ} :
    MeasurableSet {h : BanditHistory k m |
      ∀ j, armPullCount j h ≠ 0} := by
  classical
  convert MeasurableSet.iInter (fun j : Fin k ↦
    (measurableSet_eq_fun
      (measurable_armPullCount_split j)
      (measurable_const :
        Measurable (fun _ : BanditHistory k m ↦ (0 : ℝ)))).compl) using 1
  ext h
  simp

private theorem measurable_truncatedEntropy_empirical_split
    {k m : ℕ} (j : Fin k) (q : ℝ) :
    Measurable (fun h : BanditHistory k m ↦
      klucbTruncatedRelativeEntropy (armEmpiricalMean j h) q) := by
  have hemp := measurable_armEmpiricalMean_split (m := m) j
  unfold klucbTruncatedRelativeEntropy bernoulliRelativeEntropy
  apply Measurable.ite (measurableSet_le hemp measurable_const)
  · exact
      (hemp.mul ((hemp.div_const q).log)).add
        ((measurable_const.sub hemp).mul
          (((measurable_const.sub hemp).div_const (1 - q)).log))
  · exact measurable_const

private theorem measurableSet_feasibilityDichotomy_split
    {k m : ℕ} (ν : StochasticBandit k)
    (a i : Fin k) (ε : ℝ) :
    MeasurableSet {p : BanditHistory k m × (Fin k × ℝ) |
      FeasibilityDichotomy ν a i ε p.1 p.2} := by
  classical
  have hsel : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} :=
    (measurableSet_singleton i).preimage measurable_snd.fst
  have hinit : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        ∀ j, armPullCount j p.1 ≠ 0} :=
    measurableSet_initialized_split.preimage measurable_fst
  have hbudget (j : Fin k) : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        Real.log (klucbExploration (m + 1)) / armPullCount j p.1) :=
    measurable_const.div
      ((measurable_armPullCount_split j).comp measurable_fst)
  have hd (j : Fin k) : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        klucbTruncatedRelativeEntropy
          (armEmpiricalMean j p.1) (banditOptimalMean ν - ε)) :=
    (measurable_truncatedEntropy_empirical_split j
      (banditOptimalMean ν - ε)).comp measurable_fst
  have hlow : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        (¬ ∀ j, armPullCount j p.1 ≠ 0) ∨
          Real.log (klucbExploration (m + 1)) / armPullCount a p.1 <
            klucbTruncatedRelativeEntropy
              (armEmpiricalMean a p.1) (banditOptimalMean ν - ε)} :=
    hinit.compl.union (measurableSet_lt (hbudget a) (hd a))
  have hhigh : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        (∀ j, armPullCount j p.1 ≠ 0) ∧
          klucbTruncatedRelativeEntropy
              (armEmpiricalMean i p.1) (banditOptimalMean ν - ε) ≤
            Real.log (klucbExploration (m + 1)) / armPullCount i p.1} :=
    hinit.inter (measurableSet_le (hd i) (hbudget i))
  convert hsel.compl.union (hlow.union hhigh) using 1
  ext p
  by_cases hp : p.2.1 = i <;> simp [FeasibilityDichotomy, hp]

private def HistoryObeysFeasibility {k : ℕ}
    (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => True
  | m + 1, h =>
      HistoryObeysFeasibility ν a i ε (Fin.init h) ∧
        ((h (Fin.last m)).2 = 0 ∨ (h (Fin.last m)).2 = 1) ∧
        FeasibilityDichotomy ν a i ε
          (Fin.init h) (h (Fin.last m))

private theorem historyObeysFeasibility_rewards
    {k m : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k m)
    (hh : HistoryObeysFeasibility ν a i ε h) :
    HistoryRewardsBernoulli h := by
  intro t
  induction m with
  | zero => exact Fin.elim0 t
  | succ m ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) t
      · simpa [HistoryObeysFeasibility] using hh.2.1
      · have hprev :
            HistoryObeysFeasibility ν a i ε (Fin.init h) :=
          hh.1
        have hs := ih (Fin.init h) hprev s
        exact hs

private theorem measurableSet_historyObeysFeasibility_split
    {k : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    ∀ m : ℕ,
    MeasurableSet {h : BanditHistory k m |
      HistoryObeysFeasibility ν a i ε h} := by
  intro m
  induction m with
  | zero => simp [HistoryObeysFeasibility]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        fun_prop
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hreward : MeasurableSet
          {h : BanditHistory k (m + 1) |
            (h (Fin.last m)).2 = 0 ∨ (h (Fin.last m)).2 = 1} :=
        (measurableSet_eq_fun hlast.snd measurable_const).union
          (measurableSet_eq_fun hlast.snd measurable_const)
      have hpair : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            (Fin.init h, h (Fin.last m))) :=
        hinit.prodMk hlast
      change MeasurableSet
        ({h : BanditHistory k (m + 1) |
            HistoryObeysFeasibility ν a i ε (Fin.init h)} ∩
          ({h : BanditHistory k (m + 1) |
              (h (Fin.last m)).2 = 0 ∨ (h (Fin.last m)).2 = 1} ∩
            {h : BanditHistory k (m + 1) |
              FeasibilityDichotomy ν a i ε
                (Fin.init h) (h (Fin.last m))}))
      exact (ih.preimage hinit).inter
        (hreward.inter
          ((measurableSet_feasibilityDichotomy_split ν a i ε).preimage hpair))

private theorem banditMeasure_ae_historyObeysFeasibility_split
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π)
    (a i : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) (hεgap : ε < banditGap ν i) :
    ∀ m : ℕ,
    ∀ᵐ h ∂banditMeasure ν π m,
      HistoryObeysFeasibility ν a i ε h := by
  intro m
  induction m with
  | zero => simp [banditMeasure, HistoryObeysFeasibility]
  | succ m ih =>
      have hset :=
        measurableSet_historyObeysFeasibility_split ν a i ε (m + 1)
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih] with h hh
        have hrew :=
          historyObeysFeasibility_rewards ν a i ε h hh
        filter_upwards
          [banditStepKernel_ae_reward_bernoulli_split
              μvec hμ ν hν π h,
            selected_arm_feasibility_dichotomy_split
              μvec hμ ν hν π hπ a i ε ha hε hεgap h hrew]
          with z hzrew hzd
        change HistoryObeysFeasibility ν a i ε
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)
        rw [HistoryObeysFeasibility]
        simp only [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hh, hzrew, hzd⟩

private theorem prefixAt_snoc_castSucc_split
    {k n : ℕ} (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) r.castSucc =
      banditHistoryPrefixAt h r := by
  funext s
  unfold banditHistoryPrefixAt
  have hsr : s.val < r.val := by simpa using s.isLt
  have hsn : s.val < n := lt_trans hsr r.isLt
  rw [Fin.snoc]
  rw [dif_pos hsn]
  simp

private theorem prefixAt_snoc_last_split
    {k n : ℕ} (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem snoc_castSucc_split
    {k n : ℕ} (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z r.castSucc = h r := by
  simp [Fin.snoc, r.isLt]

private theorem feasibilityCount_fst_snoc_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    (klucbFeasibilityFailureCount ν a i ε
      (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)).1 =
      (klucbFeasibilityFailureCount ν a i ε h).1 +
        if z.1 = i ∧
            (¬(∀ j, armPullCount j h ≠ 0) ∨
              Real.log (klucbExploration (n + 1)) / armPullCount a h <
                klucbTruncatedRelativeEntropy (armEmpiricalMean a h)
                  (banditOptimalMean ν - ε))
          then 1 else 0 := by
  classical
  simp only [klucbFeasibilityFailureCount, Fin.sum_univ_castSucc,
    prefixAt_snoc_castSucc_split, prefixAt_snoc_last_split,
    Fin.snoc_last, snoc_castSucc_split]
  rfl

private theorem feasibilityCount_snd_snoc_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    (klucbFeasibilityFailureCount ν a i ε
      (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)).2 =
      (klucbFeasibilityFailureCount ν a i ε h).2 +
        if (∀ j, armPullCount j h ≠ 0) ∧ z.1 = i ∧
            klucbTruncatedRelativeEntropy (armEmpiricalMean i h)
                (banditOptimalMean ν - ε) ≤
              Real.log (klucbExploration (n + 1)) / armPullCount i h
          then 1 else 0 := by
  classical
  simp only [klucbFeasibilityFailureCount, Fin.sum_univ_castSucc,
    prefixAt_snoc_castSucc_split, prefixAt_snoc_last_split,
    Fin.snoc_last, snoc_castSucc_split]
  rfl

private theorem feasibilityCount_fst_nonneg_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (klucbFeasibilityFailureCount ν a i ε h).1 := by
  unfold klucbFeasibilityFailureCount
  positivity

private theorem feasibilityCount_snd_nonneg_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (klucbFeasibilityFailureCount ν a i ε h).2 := by
  unfold klucbFeasibilityFailureCount
  positivity

private theorem pullCount_le_feasibilityCount_of_obeys_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n)
    (hh : HistoryObeysFeasibility ν a i ε h) :
    (armPullCount i h : ℝ) ≤
      (klucbFeasibilityFailureCount ν a i ε h).1 +
        (klucbFeasibilityFailureCount ν a i ε h).2 := by
  induction n with
  | zero =>
      simp [armPullCount, klucbFeasibilityFailureCount]
  | succ n ih =>
      let g : BanditHistory k n := Fin.init h
      let z : Fin k × ℝ := h (Fin.last n)
      have hsnoc :
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) g z = h := by
        simpa [g, z] using Fin.snoc_init_self h
      have hhprev : HistoryObeysFeasibility ν a i ε g := by
        simpa [g, HistoryObeysFeasibility] using hh.1
      have hhdich : FeasibilityDichotomy ν a i ε g z := by
        simpa [g, z, HistoryObeysFeasibility] using hh.2.2
      have hprev := ih g hhprev
      rw [← hsnoc, armPullCount_snoc_split,
        feasibilityCount_fst_snoc_split,
        feasibilityCount_snd_snoc_split]
      push_cast
      have hU0 :
          0 ≤ (klucbFeasibilityFailureCount ν a i ε g).1 :=
        feasibilityCount_fst_nonneg_split ν a i ε g
      have hV0 :
          0 ≤ (klucbFeasibilityFailureCount ν a i ε g).2 :=
        feasibilityCount_snd_nonneg_split ν a i ε g
      by_cases hzi : z.1 = i
      · rw [if_pos hzi]
        rcases hhdich hzi with hlow | hhigh
        · rw [if_pos ⟨hzi, hlow⟩]
          have hlast :
              0 ≤
                (if (∀ j, armPullCount j g ≠ 0) ∧ z.1 = i ∧
                    klucbTruncatedRelativeEntropy (armEmpiricalMean i g)
                        (banditOptimalMean ν - ε) ≤
                      Real.log (klucbExploration (n + 1)) /
                        armPullCount i g
                  then (1 : ℝ) else 0) := by positivity
          nlinarith
        · have hhighIte :
              (if (∀ j, armPullCount j g ≠ 0) ∧ z.1 = i ∧
                    klucbTruncatedRelativeEntropy (armEmpiricalMean i g)
                        (banditOptimalMean ν - ε) ≤
                      Real.log (klucbExploration (n + 1)) /
                        armPullCount i g
                then (1 : ℝ) else 0) = 1 :=
            if_pos ⟨hhigh.1, hzi, hhigh.2⟩
          rw [hhighIte]
          have hlast :
              0 ≤
                (if z.1 = i ∧
                    (¬(∀ j, armPullCount j g ≠ 0) ∨
                      Real.log (klucbExploration (n + 1)) /
                          armPullCount a g <
                        klucbTruncatedRelativeEntropy
                          (armEmpiricalMean a g)
                          (banditOptimalMean ν - ε))
                  then (1 : ℝ) else 0) := by positivity
          nlinarith
      · rw [if_neg hzi,
          if_neg (fun hc ↦ hzi hc.1),
          if_neg (fun hc ↦ hzi hc.2.1)]
        simpa [add_zero, zero_add, add_assoc] using hprev

private theorem measurable_banditHistoryPrefixAt_split
    {k n : ℕ} (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem measurableSet_initialized_prefix_split
    {k n : ℕ} (r : Fin n) :
    MeasurableSet {h : BanditHistory k n |
      ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0} :=
  measurableSet_initialized_split.preimage
    (measurable_banditHistoryPrefixAt_split r)

private theorem measurable_feasibilityCount_fst_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).1) := by
  classical
  simp only [klucbFeasibilityFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hsel : MeasurableSet
        {h : BanditHistory k n | (h r).1 = i} :=
      measurableSet_eq_fun
        (measurable_fst.comp (measurable_pi_apply r))
        (measurable_const :
          Measurable (fun _ : BanditHistory k n ↦ i))
    have hbudget : Measurable
        (fun h : BanditHistory k n ↦
          Real.log (klucbExploration (r.val + 1)) /
            armPullCount a (banditHistoryPrefixAt h r)) :=
      measurable_const.div
        ((measurable_armPullCount_split a).comp
          (measurable_banditHistoryPrefixAt_split r))
    have hd : Measurable
        (fun h : BanditHistory k n ↦
          klucbTruncatedRelativeEntropy
            (armEmpiricalMean a (banditHistoryPrefixAt h r))
            (banditOptimalMean ν - ε)) :=
      (measurable_truncatedEntropy_empirical_split a
        (banditOptimalMean ν - ε)).comp
          (measurable_banditHistoryPrefixAt_split r)
    exact hsel.inter
      ((measurableSet_initialized_prefix_split r).compl.union
        (measurableSet_lt hbudget hd))
  · exact measurable_const
  · exact measurable_const

private theorem measurable_feasibilityCount_snd_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).2) := by
  classical
  simp only [klucbFeasibilityFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hsel : MeasurableSet
        {h : BanditHistory k n | (h r).1 = i} :=
      measurableSet_eq_fun
        (measurable_fst.comp (measurable_pi_apply r))
        (measurable_const :
          Measurable (fun _ : BanditHistory k n ↦ i))
    have hbudget : Measurable
        (fun h : BanditHistory k n ↦
          Real.log (klucbExploration (r.val + 1)) /
            armPullCount i (banditHistoryPrefixAt h r)) :=
      measurable_const.div
        ((measurable_armPullCount_split i).comp
          (measurable_banditHistoryPrefixAt_split r))
    have hd : Measurable
        (fun h : BanditHistory k n ↦
          klucbTruncatedRelativeEntropy
            (armEmpiricalMean i (banditHistoryPrefixAt h r))
            (banditOptimalMean ν - ε)) :=
      (measurable_truncatedEntropy_empirical_split i
        (banditOptimalMean ν - ε)).comp
          (measurable_banditHistoryPrefixAt_split r)
    convert ((measurableSet_initialized_prefix_split r).inter hsel).inter
      (measurableSet_le hd hbudget) using 1
    ext h
    simp [and_assoc]
  · exact measurable_const
  · exact measurable_const

private theorem feasibilityCount_fst_le_horizon_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (klucbFeasibilityFailureCount ν a i ε h).1 ≤ n := by
  classical
  unfold klucbFeasibilityFailureCount
  calc
    (∑ r : Fin n,
        if (h r).1 = i ∧
            (¬(∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∨
              Real.log (klucbExploration (r.val + 1)) /
                    armPullCount a (banditHistoryPrefixAt h r) <
                klucbTruncatedRelativeEntropy
                  (armEmpiricalMean a (banditHistoryPrefixAt h r))
                  (banditOptimalMean ν - ε))
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem feasibilityCount_snd_le_horizon_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (klucbFeasibilityFailureCount ν a i ε h).2 ≤ n := by
  classical
  unfold klucbFeasibilityFailureCount
  calc
    (∑ r : Fin n,
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            (h r).1 = i ∧
              klucbTruncatedRelativeEntropy
                  (armEmpiricalMean i (banditHistoryPrefixAt h r))
                  (banditOptimalMean ν - ε) ≤
                Real.log (klucbExploration (r.val + 1)) /
                  armPullCount i (banditHistoryPrefixAt h r)
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem integrable_feasibilityCount_fst_split
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).1)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_feasibilityCount_fst_split ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨feasibilityCount_fst_nonneg_split ν a i ε h,
        feasibilityCount_fst_le_horizon_split ν a i ε h⟩

private theorem integrable_feasibilityCount_snd_split
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).2)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_feasibilityCount_snd_split ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨feasibilityCount_snd_nonneg_split ν a i ε h,
        feasibilityCount_snd_le_horizon_split ν a i ε h⟩

end BanditAlgorithm

theorem solution {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsKLUCBPolicy π)
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hε : 0 < ε) (hεgap : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).2) := by
  have hT :=
    BanditAlgorithm.integrable_armPullCount_split (n := n) ν π i
  have hU :=
    BanditAlgorithm.integrable_feasibilityCount_fst_split
      (n := n) ν π a i ε
  have hV :=
    BanditAlgorithm.integrable_feasibilityCount_snd_split
      (n := n) ν π a i ε
  have hR :
      Integrable (fun h : BanditAlgorithm.BanditHistory k n ↦
        (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1 +
          (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).2)
        (BanditAlgorithm.banditMeasure ν π n) :=
    hU.add hV
  calc
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      ∫ h, (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1 +
          (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).2
        ∂BanditAlgorithm.banditMeasure ν π n := by
      apply integral_mono_ae hT hR
      filter_upwards
        [BanditAlgorithm.banditMeasure_ae_historyObeysFeasibility_split
          μvec hμ ν hν π hπ a i ε ha hε hεgap n] with h hh
      exact
        BanditAlgorithm.pullCount_le_feasibilityCount_of_obeys_split
          ν a i ε h hh
    _ = MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).2) := by
      exact integral_add hU hV
