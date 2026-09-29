-- Prove2me | solution 1 for BanditAlgorithm.bandit_kl_ucb_pull_count_failure_split
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T02:42:44.457091+00:00
-- url     : https://prove2.me/submissions/e7fb2fda-49a0-41a3-842f-b5f4c2b831d4

import Definitions.Def_klucbFailureCount
import Theorems.Thm_BanditAlgorithm_measurable_klucbIndex
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

private theorem banditStepKernel_ae_obeys_asymptotic_rule_split
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsKLUCBPolicy π) {m : ℕ}
    (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h,
      ((∃ j, armPullCount j h = 0) → armPullCount z.1 h = 0) ∧
      ((∀ j, armPullCount j h ≠ 0) →
        ∀ j, klucbIndex j h ≤ klucbIndex z.1 h) := by
  obtain ⟨a, hdirac, hunpulled, hmax⟩ := hπ m h
  filter_upwards
    [banditStepKernel_ae_selected_arm_split ν π h a hdirac] with z hz
  simpa [hz] using And.intro hunpulled hmax

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

private theorem measurable_klucbIndex_split
    {k m : ℕ} (i : Fin k) :
    Measurable (klucbIndex (n := m) i) := by
  exact measurable_klucbIndex i

private theorem measurableSet_asymptotic_rule_for_arm_split
    {k m : ℕ} (a : Fin k) :
    MeasurableSet {h : BanditHistory k m |
      ((∃ j, armPullCount j h = 0) → armPullCount a h = 0) ∧
      ((∀ j, armPullCount j h ≠ 0) →
        ∀ j, klucbIndex j h ≤ klucbIndex a h)} := by
  classical
  have hz (j : Fin k) :
      MeasurableSet {h : BanditHistory k m | armPullCount j h = 0} := by
    simpa only [Nat.cast_eq_zero] using
      measurableSet_eq_fun (measurable_armPullCount_split j)
        (measurable_const :
          Measurable (fun _ : BanditHistory k m ↦ (0 : ℝ)))
  have hExists :
      MeasurableSet {h : BanditHistory k m |
        ∃ j, armPullCount j h = 0} := by
    convert MeasurableSet.iUnion (fun j : Fin k ↦ hz j) using 1
    ext h
    simp
  have hAllIndex :
      MeasurableSet {h : BanditHistory k m |
        ∀ j, klucbIndex j h ≤ klucbIndex a h} := by
    convert MeasurableSet.iInter (fun j : Fin k ↦
      measurableSet_le (measurable_klucbIndex_split j)
        (measurable_klucbIndex_split a)) using 1
    ext h
    simp
  convert (hExists.compl.union (hz a)).inter
    (hExists.union hAllIndex) using 1
  ext h
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_setOf_eq]
  by_cases hex : ∃ j, armPullCount j h = 0
  · obtain ⟨j, hj⟩ := hex
    have hnall : ¬ ∀ j, armPullCount j h ≠ 0 := by
      intro hall
      exact hall j hj
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

private def LastStepObeysAsymptotic {k m : ℕ}
    (h : BanditHistory k (m + 1)) : Prop :=
  ((∃ j, armPullCount j (Fin.init h) = 0) →
      armPullCount (h (Fin.last m)).1 (Fin.init h) = 0) ∧
  ((∀ j, armPullCount j (Fin.init h) ≠ 0) →
      ∀ j, klucbIndex j (Fin.init h) ≤
        klucbIndex (h (Fin.last m)).1 (Fin.init h))

private theorem measurableSet_lastStepObeysAsymptotic_split
    {k m : ℕ} :
    MeasurableSet {h : BanditHistory k (m + 1) |
      LastStepObeysAsymptotic h} := by
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
          {q | ((∃ j, armPullCount j q = 0) →
              armPullCount a q = 0) ∧
            ((∀ j, armPullCount j q ≠ 0) →
              ∀ j, klucbIndex j q ≤
                klucbIndex a q)}) := by
    exact (measurableSet_eq_fun hlast measurable_const).inter
      ((measurableSet_asymptotic_rule_for_arm_split a).preimage hinit)
  convert MeasurableSet.iUnion (fun a : Fin k ↦ hpiece a) using 1
  ext h
  simp [LastStepObeysAsymptotic]

private def HistoryObeysAsymptotic {k : ℕ} :
    {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => True
  | m + 1, h =>
      HistoryObeysAsymptotic (Fin.init h) ∧
        LastStepObeysAsymptotic h

private theorem measurableSet_historyObeysAsymptotic_split
    {k : ℕ} : ∀ m : ℕ,
    MeasurableSet {h : BanditHistory k m | HistoryObeysAsymptotic h} := by
  intro m
  induction m with
  | zero => simp [HistoryObeysAsymptotic]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        fun_prop
      change MeasurableSet
        ({h : BanditHistory k (m + 1) |
            HistoryObeysAsymptotic (Fin.init h)} ∩
          {h : BanditHistory k (m + 1) |
            LastStepObeysAsymptotic h})
      exact (ih.preimage hinit).inter
        measurableSet_lastStepObeysAsymptotic_split

private theorem banditMeasure_ae_historyObeysAsymptotic_split
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsKLUCBPolicy π) : ∀ m : ℕ,
    ∀ᵐ h ∂banditMeasure ν π m, HistoryObeysAsymptotic h := by
  intro m
  induction m with
  | zero => simp [banditMeasure, HistoryObeysAsymptotic]
  | succ m ih =>
      have hset := measurableSet_historyObeysAsymptotic_split
        (k := k) (m + 1)
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih] with h hh
        filter_upwards
          [banditStepKernel_ae_obeys_asymptotic_rule_split ν hπ h] with z hz
        rw [HistoryObeysAsymptotic, LastStepObeysAsymptotic]
        simp only [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hh, hz⟩

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

private theorem failureCount_fst_snoc_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    (klucbFailureCount ν a i ε
      (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)).1 =
      (klucbFailureCount ν a i ε h).1 +
        if z.1 = i ∧
            (¬(∀ j, armPullCount j h ≠ 0) ∨
              klucbIndex a h ≤ banditOptimalMean ν - ε)
          then 1 else 0 := by
  classical
  simp only [klucbFailureCount, Fin.sum_univ_castSucc,
    prefixAt_snoc_castSucc_split, prefixAt_snoc_last_split,
    Fin.snoc_last, snoc_castSucc_split]


private theorem failureCount_snd_snoc_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    (klucbFailureCount ν a i ε
      (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)).2 =
      (klucbFailureCount ν a i ε h).2 +
        if (∀ j, armPullCount j h ≠ 0) ∧
            banditOptimalMean ν - ε ≤ klucbIndex i h ∧
            z.1 = i
          then 1 else 0 := by
  classical
  simp only [klucbFailureCount, Fin.sum_univ_castSucc,
    prefixAt_snoc_castSucc_split, prefixAt_snoc_last_split,
    Fin.snoc_last, snoc_castSucc_split]


private theorem failureCount_fst_nonneg_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (klucbFailureCount ν a i ε h).1 := by
  unfold klucbFailureCount
  positivity

private theorem failureCount_snd_nonneg_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (klucbFailureCount ν a i ε h).2 := by
  unfold klucbFailureCount
  positivity

private theorem pullCount_le_failureCount_of_obeys_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) (hobeys : HistoryObeysAsymptotic h) :
    (armPullCount i h : ℝ) ≤
      (klucbFailureCount ν a i ε h).1 +
        (klucbFailureCount ν a i ε h).2 := by
  induction n with
  | zero =>
      simp [armPullCount, klucbFailureCount]
  | succ n ih =>
      let g : BanditHistory k n := Fin.init h
      let z : Fin k × ℝ := h (Fin.last n)
      have hsnoc :
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) g z = h := by
        simpa [g, z] using Fin.snoc_init_self h
      have hobeys' :
          HistoryObeysAsymptotic g ∧
            (((∃ j, armPullCount j g = 0) →
                armPullCount z.1 g = 0) ∧
              ((∀ j, armPullCount j g ≠ 0) →
                ∀ j, klucbIndex j g ≤
                  klucbIndex z.1 g)) := by
        simpa [g, z, HistoryObeysAsymptotic,
          LastStepObeysAsymptotic] using hobeys
      have hprev := ih g hobeys'.1
      rw [← hsnoc, armPullCount_snoc_split,
        failureCount_fst_snoc_split, failureCount_snd_snoc_split]
      push_cast
      have hU0 :
          0 ≤ (klucbFailureCount ν a i ε g).1 :=
        failureCount_fst_nonneg_split ν a i ε g
      have hV0 :
          0 ≤ (klucbFailureCount ν a i ε g).2 :=
        failureCount_snd_nonneg_split ν a i ε g
      by_cases hzi : z.1 = i
      · rw [if_pos hzi]
        by_cases hall : ∀ j, armPullCount j g ≠ 0
        · have hdom :
              klucbIndex a g ≤ klucbIndex i g := by
            simpa [hzi] using hobeys'.2.2 hall a
          by_cases hlow :
              klucbIndex a g ≤ banditOptimalMean ν - ε
          · rw [if_pos ⟨hzi, Or.inr hlow⟩]
            have hVlast :
                0 ≤
                  (if (∀ j, armPullCount j g ≠ 0) ∧
                      banditOptimalMean ν - ε ≤
                        klucbIndex i g ∧ z.1 = i
                    then (1 : ℝ) else 0) := by positivity
            nlinarith
          · have hhigh :
                banditOptimalMean ν - ε ≤
                  klucbIndex i g :=
              (le_of_lt (lt_of_not_ge hlow)).trans hdom
            rw [if_neg (fun hc ↦ hlow
                (hc.2.elim (fun hnot ↦ (hnot hall).elim) id)),
              if_pos ⟨hall, hhigh, hzi⟩]
            nlinarith
        · rw [if_pos ⟨hzi, Or.inl hall⟩]
          have hVlast :
              0 ≤
                (if (∀ j, armPullCount j g ≠ 0) ∧
                    banditOptimalMean ν - ε ≤ klucbIndex i g ∧
                    z.1 = i then (1 : ℝ) else 0) := by positivity
          nlinarith
      · rw [if_neg hzi]
        rw [if_neg (fun hc ↦ hzi hc.1),
          if_neg (fun hc ↦ hzi hc.2.2)]
        simpa [add_zero, zero_add, add_assoc] using hprev

private theorem measurable_banditHistoryPrefixAt_split
    {k n : ℕ} (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem measurableSet_initialized_split
    {k n : ℕ} (r : Fin n) :
    MeasurableSet {h : BanditHistory k n |
      ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0} := by
  classical
  convert MeasurableSet.iInter (fun j : Fin k ↦
    (measurableSet_eq_fun
      ((measurable_armPullCount_split j).comp
        (measurable_banditHistoryPrefixAt_split r))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (0 : ℝ)))).compl) using 1
  ext h
  simp

private theorem measurable_failureCount_fst_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFailureCount ν a i ε h).1) := by
  classical
  simp only [klucbFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hsel : MeasurableSet
        {h : BanditHistory k n | (h r).1 = i} :=
      measurableSet_eq_fun
        (measurable_fst.comp (measurable_pi_apply r))
        (measurable_const :
          Measurable (fun _ : BanditHistory k n ↦ i))
    have hbad : MeasurableSet
        {h : BanditHistory k n |
          ¬(∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∨
            klucbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε} :=
      (measurableSet_initialized_split r).compl.union
        (measurableSet_le
          ((measurable_klucbIndex_split a).comp
            (measurable_banditHistoryPrefixAt_split r))
          measurable_const)
    exact hsel.inter hbad
  · exact measurable_const
  · exact measurable_const

private theorem measurable_failureCount_snd_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFailureCount ν a i ε h).2) := by
  classical
  simp only [klucbFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hm := ((measurableSet_initialized_split r).inter
        (measurableSet_le
          (measurable_const :
            Measurable (fun _ : BanditHistory k n ↦
              banditOptimalMean ν - ε))
          ((measurable_klucbIndex_split i).comp
            (measurable_banditHistoryPrefixAt_split r)))).inter
        (measurableSet_eq_fun
          (measurable_fst.comp (measurable_pi_apply r))
          (measurable_const :
            Measurable (fun _ : BanditHistory k n ↦ i)))
    convert hm using 1
    ext h
    simp [and_assoc]
  · exact measurable_const
  · exact measurable_const

private theorem failureCount_fst_le_horizon_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (klucbFailureCount ν a i ε h).1 ≤ n := by
  classical
  unfold klucbFailureCount
  calc
    (∑ r : Fin n,
        if (h r).1 = i ∧
            (¬(∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∨
              klucbIndex a (banditHistoryPrefixAt h r) ≤
                banditOptimalMean ν - ε)
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem failureCount_snd_le_horizon_split
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (klucbFailureCount ν a i ε h).2 ≤ n := by
  classical
  unfold klucbFailureCount
  calc
    (∑ r : Fin n,
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            banditOptimalMean ν - ε ≤
              klucbIndex i (banditHistoryPrefixAt h r) ∧
            (h r).1 = i
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem integrable_failureCount_fst_split
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFailureCount ν a i ε h).1)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_failureCount_fst_split ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨failureCount_fst_nonneg_split ν a i ε h,
        failureCount_fst_le_horizon_split ν a i ε h⟩

private theorem integrable_failureCount_snd_split
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFailureCount ν a i ε h).2)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_failureCount_snd_split ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨failureCount_snd_nonneg_split ν a i ε h,
        failureCount_snd_le_horizon_split ν a i ε h⟩

end BanditAlgorithm

theorem solution {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsKLUCBPolicy π)
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFailureCount ν a i ε h).2) := by
  have hT :=
    BanditAlgorithm.integrable_armPullCount_split (n := n) ν π i
  have hU :=
    BanditAlgorithm.integrable_failureCount_fst_split (n := n) ν π a i ε
  have hV :=
    BanditAlgorithm.integrable_failureCount_snd_split (n := n) ν π a i ε
  have hR :
      Integrable (fun h : BanditAlgorithm.BanditHistory k n ↦
        (BanditAlgorithm.klucbFailureCount ν a i ε h).1 +
          (BanditAlgorithm.klucbFailureCount ν a i ε h).2)
        (BanditAlgorithm.banditMeasure ν π n) :=
    hU.add hV
  calc
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      ∫ h, (BanditAlgorithm.klucbFailureCount ν a i ε h).1 +
          (BanditAlgorithm.klucbFailureCount ν a i ε h).2
        ∂BanditAlgorithm.banditMeasure ν π n := by
      apply integral_mono_ae hT hR
      filter_upwards
        [BanditAlgorithm.banditMeasure_ae_historyObeysAsymptotic_split
          ν hπ n] with h hh
      exact
        BanditAlgorithm.pullCount_le_failureCount_of_obeys_split
          ν a i ε h hh
    _ = MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFailureCount ν a i ε h).2) := by
      exact integral_add hU hV
