-- Prove2me | solution 1 for BanditAlgorithm.asymptotic_ucb_optimal_underestimation_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T15:37:23.007832+00:00
-- url     : https://prove2.me/submissions/7a7c6831-e2c7-4846-aff8-96eba0cccf43

import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_schedule_reciprocal_sum_bound
import Definitions.Def_asymptoticUcbFailureCount
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator_under {k n : ℕ}
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

private theorem measurable_armPullCount_under {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  simp_rw [pullCount_cast_eq_sum_indicator_under]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite
    ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

private theorem armPullCount_snoc_under {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, pullCount_cast_eq_sum_indicator_under,
    pullCount_cast_eq_sum_indicator_under i h, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armPullCount_le_horizon_under {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    armPullCount i h ≤ n := by
  rw [armPullCount]
  calc
    {t | (h t).1 = i}.toFinset.card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := Fintype.card_fin n

private theorem measurable_armEmpiricalMean_under {k m : ℕ} (i : Fin k) :
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
  exact hnum.div (measurable_armPullCount_under i)

private theorem measurable_asymptoticUcbIndex_under
    {k m : ℕ} (i : Fin k) :
    Measurable (asymptoticUcbIndex (n := m) i) := by
  unfold asymptoticUcbIndex
  apply (measurable_armEmpiricalMean_under i).add
  exact Measurable.sqrt
    (measurable_const.div (measurable_armPullCount_under i))

private theorem measurable_banditHistoryPrefixAt_under
    {k n : ℕ} (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem measurableSet_initialized_under
    {k m : ℕ} :
    MeasurableSet {h : BanditHistory k m |
      ∀ j, armPullCount j h ≠ 0} := by
  classical
  convert MeasurableSet.iInter (fun j : Fin k ↦
    (measurableSet_eq_fun
      (measurable_armPullCount_under j)
      (measurable_const :
        Measurable (fun _ : BanditHistory k m ↦ (0 : ℝ)))).compl) using 1
  ext h
  simp

private theorem measurableSet_lowOptimal_under
    {k m : ℕ} (ν : StochasticBandit k) (a : Fin k) (ε : ℝ) :
    MeasurableSet {h : BanditHistory k m |
      (∀ j, armPullCount j h ≠ 0) ∧
        asymptoticUcbIndex a h ≤ banditOptimalMean ν - ε} :=
  measurableSet_initialized_under.inter
    (measurableSet_le (measurable_asymptoticUcbIndex_under a)
      measurable_const)

private theorem prefixAt_snoc_castSucc_under {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
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

private theorem prefixAt_snoc_last_under {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem banditMeasure_map_init_under {k m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) :
    (banditMeasure ν π (m + 1)).map
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) =
      banditMeasure ν π m := by
  rw [banditMeasure]
  rw [MeasureTheory.Measure.map_map
    (by fun_prop :
      Measurable (fun h : BanditHistory k (m + 1) ↦ Fin.init h))
    measurable_banditHistorySnoc]
  have hfun :
      ((fun h : BanditHistory k (m + 1) ↦ Fin.init h) ∘
        (fun h : BanditHistory k m × (Fin k × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) h.1 h.2)) =
        Prod.fst := by
    funext p
    simp
  rw [hfun]
  change Measure.fst
      ((banditMeasure ν π m).compProd (banditStepKernel ν π m)) =
    banditMeasure ν π m
  exact MeasureTheory.Measure.fst_compProd
    (banditMeasure ν π m) (banditStepKernel ν π m)

private theorem banditMeasure_map_historyPrefixAt_under
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) :
    (banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) =
      banditMeasure ν π r.val := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h (Fin.last n)) =
            banditMeasure ν π n
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h (Fin.last n)) =
          (fun h ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa using
              prefixAt_snoc_last_under (Fin.init h) (h (Fin.last n))]
        exact banditMeasure_map_init_under ν π
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h s.castSucc) =
            banditMeasure ν π s.val
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h s.castSucc) =
          (fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
            (fun h : BanditHistory k (n + 1) ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa [Function.comp_apply] using
              prefixAt_snoc_castSucc_under
                (Fin.init h) (h (Fin.last n)) s]
        calc
          (banditMeasure ν π (n + 1)).map
              ((fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)) =
              ((banditMeasure ν π (n + 1)).map
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)).map
                (fun g : BanditHistory k n ↦
                  banditHistoryPrefixAt g s) := by
            symm
            exact MeasureTheory.Measure.map_map
              (measurable_banditHistoryPrefixAt_under s)
              (by fun_prop :
                Measurable
                  (fun h : BanditHistory k (n + 1) ↦ Fin.init h))
          _ = banditMeasure ν π s.val := by
            rw [banditMeasure_map_init_under ν π, ih s]

private theorem armStoppedCenteredSum_snoc_under {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

private noncomputable def armCenteredSumUnder {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

private theorem armCenteredSumUnder_snoc {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armCenteredSumUnder ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSumUnder ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSumUnder, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armStoppedCenteredSum_eq_pullCount_mul_under
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  classical
  have hstop :
      armStoppedCenteredSum ν i u m h = armCenteredSumUnder ν i h := by
    induction m with
    | zero => simp [armStoppedCenteredSum, armCenteredSumUnder]
    | succ m ih =>
        rw [← Fin.snoc_init_self h] at hcount ⊢
        rw [armPullCount_snoc_under] at hcount
        rw [armStoppedCenteredSum_snoc_under, armCenteredSumUnder_snoc]
        by_cases hi : (h (Fin.last m)).1 = i
        · have hprev : armPullCount i (Fin.init h) < u := by
            simp [hi] at hcount
            omega
          rw [if_pos ⟨hprev, hi⟩, if_pos hi,
            ih (Fin.init h) (Nat.le_of_lt hprev)]
        · have hprev : armPullCount i (Fin.init h) ≤ u := by
            simpa [hi] using hcount
          rw [if_neg (fun hc ↦ hi hc.2), if_neg hi,
            ih (Fin.init h) hprev]
  rw [hstop]
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSumUnder, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

private theorem measureReal_biUnion_finset_le_under
    {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (I : Finset ι) (s : ι → Set Ω) :
    P.real (⋃ i ∈ I, s i) ≤ ∑ i ∈ I, P.real (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi]
      have hset :
          (⋃ j ∈ insert i I, s j) = s i ∪ ⋃ j ∈ I, s j := by
        ext x
        simp [or_assoc]
      rw [hset]
      exact (measureReal_union_le _ _).trans
        (add_le_add (le_refl _) ih)

private theorem exp_neg_mul_sum_Icc_le_inv_under
    (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∑ s ∈ Finset.Icc 1 n, Real.exp (-(s : ℝ) * a) ≤ 1 / a := by
  let q : ℝ := Real.exp (-a)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_add_one_iff]
  have hsum : ∑ s ∈ Finset.Icc 1 n, q ^ s ≤ q / (1 - q) := by
    rw [le_div_iff₀ hden]
    rw [hIcc, geom_sum_Ico_mul_neg q (by omega : 1 ≤ n + 1)]
    have hpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq0 _
    simp only [pow_one]
    linarith
  have hqa : q / (1 - q) ≤ 1 / a := by
    have hqpos : 0 < q := Real.exp_pos _
    have hea : 1 + a ≤ Real.exp a := by
      simpa [add_comm] using Real.add_one_le_exp a
    have hmain : a * q ≤ 1 - q := by
      have := mul_le_mul_of_nonneg_right hea hqpos.le
      dsimp [q] at this ⊢
      rw [← Real.exp_add] at this
      norm_num at this
      linarith
    rw [div_le_div_iff₀ hden ha]
    nlinarith
  calc
    ∑ s ∈ Finset.Icc 1 n, Real.exp (-(s : ℝ) * a) =
        ∑ s ∈ Finset.Icc 1 n, q ^ s := by
      apply Finset.sum_congr rfl
      intro s hs
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ q / (1 - q) := hsum
    _ ≤ 1 / a := hqa

private theorem exp_neg_half_sq_sum_Icc_le_under
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∑ s ∈ Finset.Icc 1 n, Real.exp (-((s : ℝ) * ε ^ 2) / 2) ≤
      2 / ε ^ 2 := by
  have ha : 0 < ε ^ 2 / 2 := by positivity
  have h := exp_neg_mul_sum_Icc_le_inv_under n ha
  have hεne : ε ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hε)
  calc
    ∑ s ∈ Finset.Icc 1 n, Real.exp (-((s : ℝ) * ε ^ 2) / 2) =
        ∑ s ∈ Finset.Icc 1 n, Real.exp (-(s : ℝ) * (ε ^ 2 / 2)) := by
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      ring
    _ ≤ 1 / (ε ^ 2 / 2) := h
    _ = 2 / ε ^ 2 := by field_simp [hεne]

private theorem asymptoticUcbSchedule_pos_under (t : ℕ) :
    0 < asymptoticUcbSchedule t := by
  simp only [asymptoticUcbSchedule]
  positivity

private theorem asymptoticUcbSchedule_log_nonneg_under (t : ℕ) :
    0 ≤ Real.log (asymptoticUcbSchedule t) := by
  apply Real.log_nonneg
  simp only [asymptoticUcbSchedule]
  nlinarith [mul_nonneg (Nat.cast_nonneg t) (sq_nonneg (Real.log t))]

private theorem exp_low_threshold_le_under
    (t u : ℕ) (hu : 1 ≤ u) {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-(u : ℝ) *
        (ε + Real.sqrt
          (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ))) ^ 2 / 2) ≤
      1 / asymptoticUcbSchedule t *
        Real.exp (-((u : ℝ) * ε ^ 2) / 2) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hL : 0 ≤ Real.log (asymptoticUcbSchedule t) :=
    asymptoticUcbSchedule_log_nonneg_under t
  have hq : 0 ≤
      2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt
      (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ)) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt
          (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ)) ^ 2 =
        2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ) :=
    Real.sq_sqrt hq
  have harg :
      -(u : ℝ) *
          (ε + Real.sqrt
            (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ))) ^ 2 / 2 ≤
        -Real.log (asymptoticUcbSchedule t) -
          (u : ℝ) * ε ^ 2 / 2 := by
    rw [add_sq, hsqrt_sq]
    have hcross : 0 ≤ ε * Real.sqrt
        (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ)) :=
      mul_nonneg hε.le hsqrt
    field_simp [ne_of_gt huR]
    nlinarith
  calc
    Real.exp (-(u : ℝ) *
        (ε + Real.sqrt
          (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ))) ^ 2 / 2) ≤
        Real.exp (-Real.log (asymptoticUcbSchedule t) -
          (u : ℝ) * ε ^ 2 / 2) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (-Real.log (asymptoticUcbSchedule t)) *
        Real.exp (-((u : ℝ) * ε ^ 2) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = 1 / asymptoticUcbSchedule t *
        Real.exp (-((u : ℝ) * ε ^ 2) / 2) := by
      rw [Real.exp_neg, Real.exp_log (asymptoticUcbSchedule_pos_under t)]
      simp only [one_div]

private theorem lowOptimal_probability_le_under
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit 1 ν) {π : BanditPolicy k}
    (r : Fin n) (a : Fin k) {ε : ℝ}
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε} ≤
      1 / asymptoticUcbSchedule (r.val + 1) *
        (∑ u ∈ Finset.Icc 1 r.val,
          Real.exp (-((u : ℝ) * ε ^ 2) / 2)) := by
  let A : Set (BanditHistory k r.val) :=
    {g |
      (∀ j, armPullCount j g ≠ 0) ∧
        asymptoticUcbIndex a g ≤ banditOptimalMean ν - ε}
  let threshold : ℕ → ℝ := fun u ↦
    ε + Real.sqrt
      (2 * Real.log (asymptoticUcbSchedule (r.val + 1)) / (u : ℝ))
  let B : ℕ → Set (BanditHistory k r.val) := fun u ↦
    {g | armStoppedCenteredSum ν a u r.val g ≤ -(u : ℝ) * threshold u}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lowOptimal_under ν a ε
  have hsubset : A ⊆ ⋃ u ∈ Finset.Icc 1 r.val, B u := by
    intro g hg
    have hcount_ne : armPullCount a g ≠ 0 := hg.1 a
    let u : ℕ := armPullCount a g
    have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hcount_ne
    have hur : u ≤ r.val := armPullCount_le_horizon_under a g
    apply Set.mem_iUnion.2
    refine ⟨u, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_Icc.mpr ⟨hu1, hur⟩
    · dsimp [B, threshold]
      rw [armStoppedCenteredSum_eq_pullCount_mul_under ν a u g (le_refl u)]
      have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
      have hindex := hg.2
      rw [← ha] at hindex
      unfold asymptoticUcbIndex at hindex
      change armEmpiricalMean a g +
          Real.sqrt
            (2 * Real.log (asymptoticUcbSchedule (r.val + 1)) /
              (armPullCount a g : ℝ)) ≤
            banditArmMean ν a - ε at hindex
      change (armPullCount a g : ℝ) *
          (armEmpiricalMean a g - banditArmMean ν a) ≤
        -(armPullCount a g : ℝ) *
          (ε + Real.sqrt
            (2 * Real.log (asymptoticUcbSchedule (r.val + 1)) /
              (armPullCount a g : ℝ)))
      nlinarith
  have hmap_apply :
      ((banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r)).real A =
        (banditMeasure ν π n).real
          ((fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) ⁻¹' A) := by
    simpa [Measure.real] using congrArg ENNReal.toReal
      (Measure.map_apply (measurable_banditHistoryPrefixAt_under r) hA)
  have htail (u : ℕ) (hu : u ∈ Finset.Icc 1 r.val) :
      (banditMeasure ν π r.val).real (B u) ≤
        1 / asymptoticUcbSchedule (r.val + 1) *
          Real.exp (-((u : ℝ) * ε ^ 2) / 2) := by
    have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
    have hthreshold : 0 ≤ threshold u := by
      dsimp [threshold]
      positivity
    have hraw :=
      (bandit_adaptive_stopped_centered_sum_tail
        (n := r.val) ν hν (π := π) a u hthreshold).2
    exact hraw.trans
      (exp_low_threshold_le_under (r.val + 1) u hu1 hε)
  change (banditMeasure ν π n).real
      ((fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) ⁻¹' A) ≤ _
  calc
    (banditMeasure ν π n).real
        ((fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) ⁻¹' A) =
        ((banditMeasure ν π n).map
          (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r)).real A :=
      hmap_apply.symm
    _ = (banditMeasure ν π r.val).real A := by
      rw [banditMeasure_map_historyPrefixAt_under ν π r]
    _ ≤ (banditMeasure ν π r.val).real
        (⋃ u ∈ Finset.Icc 1 r.val, B u) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ u ∈ Finset.Icc 1 r.val,
        (banditMeasure ν π r.val).real (B u) :=
      measureReal_biUnion_finset_le_under
        (banditMeasure ν π r.val) (Finset.Icc 1 r.val) B
    _ ≤ ∑ u ∈ Finset.Icc 1 r.val,
        (1 / asymptoticUcbSchedule (r.val + 1) *
          Real.exp (-((u : ℝ) * ε ^ 2) / 2)) := by
      exact Finset.sum_le_sum fun u hu ↦ htail u hu
    _ = 1 / asymptoticUcbSchedule (r.val + 1) *
        (∑ u ∈ Finset.Icc 1 r.val,
          Real.exp (-((u : ℝ) * ε ^ 2) / 2)) := by
      rw [Finset.mul_sum]

private theorem measurableSet_lowOptimal_prefix_under
    {k n : ℕ} (ν : StochasticBandit k) (r : Fin n)
    (a : Fin k) (ε : ℝ) :
    MeasurableSet
      {h : BanditHistory k n |
        (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
          asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
            banditOptimalMean ν - ε} :=
  (measurableSet_lowOptimal_under ν a ε).preimage
    (measurable_banditHistoryPrefixAt_under r)

private theorem integrable_lowOptimal_indicator_under
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) (a : Fin k) (ε : ℝ) :
    Integrable
      (fun h : BanditHistory k n ↦
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε
          then (1 : ℝ) else 0)
      (banditMeasure ν π n) := by
  have hm : Measurable
      (fun h : BanditHistory k n ↦
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε
          then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lowOptimal_prefix_under ν r a ε)
      measurable_const measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun h ↦ by
    split <;> norm_num

private theorem integral_lowOptimal_indicator_eq_probability_under
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) (a : Fin k) (ε : ℝ) :
    (∫ h,
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε
          then (1 : ℝ) else 0
      ∂banditMeasure ν π n) =
      (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε} := by
  let E : Set (BanditHistory k n) :=
    {h |
      (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
        asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
          banditOptimalMean ν - ε}
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_lowOptimal_prefix_under ν r a ε
  have hfun :
      (fun h : BanditHistory k n ↦
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
              banditOptimalMean ν - ε
          then (1 : ℝ) else 0) =
        E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext h
    change (if h ∈ E then (1 : ℝ) else 0) =
      E.indicator (fun _ ↦ (1 : ℝ)) h
    by_cases hh : h ∈ E <;> simp [Set.indicator, hh]
  rw [hfun]
  change (∫ h, E.indicator (fun _ ↦ (1 : ℝ)) h
      ∂banditMeasure ν π n) =
    (banditMeasure ν π n).real E
  exact integral_indicator_one hE

private theorem sum_fin_schedule_reciprocal_eq_under (n : ℕ) :
    (∑ r : Fin n, 1 / asymptoticUcbSchedule (r.val + 1)) =
      ∑ t ∈ Finset.Icc 1 n, 1 / asymptoticUcbSchedule t := by
  change (∑ r : Fin n,
      (fun x : ℕ ↦ 1 / asymptoticUcbSchedule (x + 1)) r) =
    ∑ t ∈ Finset.Icc 1 n, 1 / asymptoticUcbSchedule t
  rw [Fin.sum_univ_eq_sum_range
    (fun x : ℕ ↦ 1 / asymptoticUcbSchedule (x + 1)) n]
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_add_one_iff]
  rw [hIcc]
  rw [← Finset.sum_Ico_add'
    (fun t : ℕ ↦ 1 / asymptoticUcbSchedule t) 0 n 1]
  simp only [Nat.zero_add, Nat.Ico_zero_eq_range]

theorem asymptotic_ucb_optimal_underestimation_count_bound_proof
    {k : ℕ} {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) :
    integral (banditMeasure ν π n)
        (fun h ↦ (asymptoticUcbFailureCount ν a i ε h).1) ≤
      5 / ε ^ 2 := by
  classical
  have hround (r : Fin n) :
      (∫ h,
          if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
              asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
                banditOptimalMean ν - ε
            then (1 : ℝ) else 0
        ∂banditMeasure ν π n) ≤
        1 / asymptoticUcbSchedule (r.val + 1) * (2 / ε ^ 2) := by
    rw [integral_lowOptimal_indicator_eq_probability_under ν π r a ε]
    calc
      (banditMeasure ν π n).real
          {h : BanditHistory k n |
            (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
              asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
                banditOptimalMean ν - ε} ≤
          1 / asymptoticUcbSchedule (r.val + 1) *
            (∑ u ∈ Finset.Icc 1 r.val,
              Real.exp (-((u : ℝ) * ε ^ 2) / 2)) :=
        lowOptimal_probability_le_under ν hν r a ha hε
      _ ≤ 1 / asymptoticUcbSchedule (r.val + 1) * (2 / ε ^ 2) := by
        apply mul_le_mul_of_nonneg_left
          (exp_neg_half_sq_sum_Icc_le_under r.val hε)
        exact one_div_nonneg.mpr
          (asymptoticUcbSchedule_pos_under (r.val + 1)).le
  simp only [asymptoticUcbFailureCount]
  rw [integral_finset_sum]
  · calc
      (∑ r : Fin n,
          ∫ h,
            (if (∀ j,
                  armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
                asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
                  banditOptimalMean ν - ε
              then (1 : ℝ) else 0)
            ∂banditMeasure ν π n) ≤
          ∑ r : Fin n,
            (1 / asymptoticUcbSchedule (r.val + 1) * (2 / ε ^ 2)) :=
        Finset.sum_le_sum fun r hr ↦ hround r
      _ = (∑ r : Fin n, 1 / asymptoticUcbSchedule (r.val + 1)) *
          (2 / ε ^ 2) := by rw [Finset.sum_mul]
      _ = (∑ t ∈ Finset.Icc 1 n, 1 / asymptoticUcbSchedule t) *
          (2 / ε ^ 2) := by rw [sum_fin_schedule_reciprocal_eq_under]
      _ ≤ (5 / 2) * (2 / ε ^ 2) := by
        apply mul_le_mul_of_nonneg_right
          (asymptotic_ucb_schedule_reciprocal_sum_bound n)
        positivity
      _ = 5 / ε ^ 2 := by ring
  · intro r hr
    exact integrable_lowOptimal_indicator_under ν π r a ε

end BanditAlgorithm

theorem solution
    {k : ℕ} {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hε : 0 < ε) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.asymptoticUcbFailureCount ν a i ε h).1) ≤
      5 / ε ^ 2 :=
  BanditAlgorithm.asymptotic_ucb_optimal_underestimation_count_bound_proof
    hν n a i ε ha hε
