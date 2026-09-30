-- Prove2me | solution 1 for BanditAlgorithm.measurable_klucbIndex
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:06:15.734804+00:00
-- url     : https://prove2.me/submissions/03d0508f-d5e8-4a20-93a7-3b8ad02cc9f3

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy

open Set

namespace KLUCBMeasurability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem isClosed_exists_interval (f : X → ℝ → ℝ)
    (hf : ContinuousOn (fun p : X × ℝ => f p.1 p.2) (univ ×ˢ Ioo 0 1))
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    IsClosed {x | ∃ q ∈ Icc a b, f x q ≤ 0} := by
  let K := Icc a b
  have hK : IsCompact K := isCompact_Icc
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : X × K => f p.1 p.2) := by
    apply hf.comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    intro p
    exact ⟨mem_univ _, lt_of_lt_of_le ha p.2.property.1,
      lt_of_le_of_lt p.2.property.2 hb⟩
  have hclosed := isClosedMap_fst_of_compactSpace
    {p : X × K | f p.1 p.2 ≤ 0} (isClosed_le hc continuous_const)
  convert hclosed using 1
  ext x
  constructor
  · rintro ⟨q, hq, hfq⟩
    exact ⟨(x, ⟨q, hq⟩), hfq, rfl⟩
  · rintro ⟨⟨y, q⟩, hfq, rfl⟩
    exact ⟨q, q.property, hfq⟩

def augmentedFeasible (f : X → ℝ → ℝ) (A : Set X) (x : X) : Set ℝ :=
  insert 0 ({q | q ∈ Ioo 0 1 ∧ f x q ≤ 0} ∪ {q | q = 1 ∧ x ∈ A})

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem augmentedFeasible_bddAbove (f : X → ℝ → ℝ) (A : Set X) (x : X) :
    BddAbove (augmentedFeasible f A x) := by
  refine ⟨1, ?_⟩
  rintro q (rfl | h | h)
  · norm_num
  · exact h.1.2.le
  · exact h.1.le

theorem measurable_sup_augmented (f : X → ℝ → ℝ)
    (hf : ContinuousOn (fun p : X × ℝ => f p.1 p.2) (univ ×ˢ Ioo 0 1))
    (A : Set X) (hA : MeasurableSet A) :
    Measurable (fun x => sSup (augmentedFeasible f A x)) := by
  apply measurable_of_Ioi
  intro a
  have hsup (x : X) : a < sSup (augmentedFeasible f A x) ↔
      ∃ q ∈ augmentedFeasible f A x, a < q :=
    lt_csSup_iff (augmentedFeasible_bddAbove f A x) ⟨0, mem_insert _ _⟩
  by_cases ha : a < 0
  · have heq : (fun x => sSup (augmentedFeasible f A x)) ⁻¹' Ioi a = univ := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact (hsup x).2 ⟨0, mem_insert _ _, ha⟩
    rw [heq]
    exact MeasurableSet.univ
  · have ha : 0 ≤ a := le_of_not_gt ha
    -- Rational compact intervals capture every interior witness above the threshold.
    have heq : (fun x => sSup (augmentedFeasible f A x)) ⁻¹' Ioi a =
        {x | a < 1 ∧ x ∈ A} ∪
          ⋃ i : ℚ, ⋃ j : ℚ, ⋃ (_ : 0 < (i : ℝ) ∧ a < i ∧ (j : ℝ) < 1),
            {x | ∃ q ∈ Icc (i : ℝ) (j : ℝ), f x q ≤ 0} := by
      ext x
      simp only [mem_preimage, mem_Ioi, hsup, mem_union, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨q, hq, haq⟩
        rcases hq with rfl | hq | hq
        · exact (not_lt_of_ge ha haq).elim
        · right
          obtain ⟨i, hai, hiq⟩ := exists_rat_btwn haq
          obtain ⟨j, hqj, hj⟩ := exists_rat_btwn hq.1.2
          exact ⟨i, j, ⟨lt_of_le_of_lt ha hai, hai, hj⟩, q, ⟨hiq.le, hqj.le⟩, hq.2⟩
        · exact Or.inl ⟨hq.1 ▸ haq, hq.2⟩
      · rintro (⟨ha1, hx⟩ | ⟨i, j, hij, q, hq, hfq⟩)
        · exact ⟨1, Or.inr (Or.inr ⟨rfl, hx⟩), ha1⟩
        · exact ⟨q, Or.inr (Or.inl
            ⟨⟨lt_of_lt_of_le hij.1 hq.1, lt_of_le_of_lt hq.2 hij.2.2⟩, hfq⟩),
            lt_of_lt_of_le hij.2.1 hq.1⟩
    rw [heq]
    apply MeasurableSet.union
    · by_cases h : a < 1
      · simpa [h] using hA
      · simp only [h, false_and, ofPred_false, MeasurableSet.empty]
    · exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
        MeasurableSet.iUnion fun h => (isClosed_exists_interval f hf i j h.1 h.2.2).measurableSet

end KLUCBMeasurability

open Set MeasureTheory ProbabilityTheory

namespace KLUCBMeasurability

theorem mul_log_div (p q : ℝ) (hq : q ≠ 0) :
    p * Real.log (p / q) = p * Real.log p - p * Real.log q := by
  by_cases hp : p = 0
  · simp [hp]
  · rw [Real.log_div hp hq, mul_sub]

theorem continuousOn_entropy :
    ContinuousOn (fun z : (ℝ × ℝ) × ℝ =>
      BanditAlgorithm.bernoulliRelativeEntropy z.1.1 z.2 - z.1.2)
      (univ ×ˢ Ioo 0 1) := by
  have hp : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1.2) :=
    continuous_snd.comp continuous_fst
  have h1p : Continuous (fun z : (ℝ × ℝ) × ℝ => 1 - z.1.1) :=
    continuous_const.sub hp
  have hq : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => Real.log z.2)
      (univ ×ˢ Ioo 0 1) :=
    continuous_snd.continuousOn.log fun z hz => ne_of_gt hz.2.1
  have h1q : ContinuousOn (fun z : (ℝ × ℝ) × ℝ => Real.log (1 - z.2))
      (univ ×ˢ Ioo 0 1) :=
    (continuous_const.sub continuous_snd).continuousOn.log fun z hz =>
      ne_of_gt (sub_pos.mpr hz.2.2)
  have h := (((Real.continuous_mul_log.comp hp).continuousOn.sub (hp.continuousOn.mul hq)).add
    ((Real.continuous_mul_log.comp h1p).continuousOn.sub
      (h1p.continuousOn.mul h1q))).sub hc.continuousOn
  apply h.congr
  intro z hz
  simp only [BanditAlgorithm.bernoulliRelativeEntropy,
    mul_log_div _ _ (ne_of_gt hz.2.1),
    mul_log_div _ _ (ne_of_gt (sub_pos.mpr hz.2.2))]
  rfl

def feasible (p c : ℝ) : Set ℝ :=
  {q ∈ Icc 0 1 | BanditAlgorithm.bernoulliRelativeEntropy p q ≤ c ∧
    (q = 0 → p = 0) ∧ (q = 1 → p = 1)}

theorem sup_insert_zero (s : Set ℝ) (hs : s ⊆ Ici 0) (hb : BddAbove s) :
    sSup (insert 0 s) = sSup s := by
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp [Real.sSup_empty]
  · rw [csSup_insert hb hn, sup_eq_right]
    obtain ⟨x, hx⟩ := hn
    exact le_trans (hs hx) (le_csSup hb hx)

theorem insert_zero_feasible (p c : ℝ) :
    insert 0 (feasible p c) =
      augmentedFeasible
        (fun z : ℝ × ℝ => fun q => BanditAlgorithm.bernoulliRelativeEntropy z.1 q - z.2)
        {z | z.1 = 1 ∧ 0 ≤ z.2} (p, c) := by
  ext q
  simp only [augmentedFeasible, feasible, mem_insert_iff, mem_union, mem_ofPred_eq,
    mem_Icc, mem_Ioo, sub_nonpos]
  constructor
  · rintro (rfl | ⟨hq, hd, hzero, hone⟩)
    · exact Or.inl rfl
    · by_cases hq0 : q = 0
      · exact Or.inl hq0
      · right
        by_cases hq1 : q = 1
        · right
          have hp := hone hq1
          refine ⟨hq1, hp, ?_⟩
          simpa [hp, hq1, BanditAlgorithm.bernoulliRelativeEntropy] using hd
        · exact Or.inl ⟨⟨lt_of_le_of_ne hq.1 (Ne.symm hq0),
            lt_of_le_of_ne hq.2 hq1⟩, hd⟩
  · rintro (h | ⟨hq, hd⟩ | ⟨rfl, rfl, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨hq.1.le, hq.2.le⟩, hd,
        fun h => (ne_of_gt hq.1 h).elim, fun h => (ne_of_lt hq.2 h).elim⟩
    · right
      simpa [BanditAlgorithm.bernoulliRelativeEntropy] using hc

theorem measurable_scalarIndex : Measurable (fun z : ℝ × ℝ => sSup (feasible z.1 z.2)) := by
  -- Adding zero does not change this nonnegative supremum, including the empty case.
  have hA : MeasurableSet {z : ℝ × ℝ | z.1 = 1 ∧ 0 ≤ z.2} :=
    ((isClosed_eq continuous_fst continuous_const).inter
      (isClosed_le continuous_const continuous_snd)).measurableSet
  have h := measurable_sup_augmented
    (fun z : ℝ × ℝ => fun q => BanditAlgorithm.bernoulliRelativeEntropy z.1 q - z.2)
    continuousOn_entropy _ hA
  convert h using 1
  funext z
  rw [← insert_zero_feasible]
  symm
  apply sup_insert_zero
  · intro q hq
    exact hq.1.1
  · exact ⟨1, fun q hq => hq.1.2⟩

end KLUCBMeasurability

namespace BanditAlgorithm

theorem measurable_armPullCount_local {k n : ℕ} (i : Fin k) :
    Measurable (armPullCount (n := n) i) := by
  classical
  have heq : armPullCount (n := n) i =
      fun h => ∑ t : Fin n, if (h t).1 = i then (1 : ℕ) else 0 := by
    funext h
    simp [armPullCount, Set.toFinset_ofPred, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro t ht
  have hm : Measurable (fun h : BanditHistory k n => (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const measurable_const

theorem measurable_armEmpiricalMean_local {k n : ℕ} (i : Fin k) :
    Measurable (armEmpiricalMean (n := n) i) := by
  classical
  have heq : armEmpiricalMean (n := n) i = fun h =>
      (∑ t : Fin n, if (h t).1 = i then (h t).2 else 0) / armPullCount i h := by
    funext h
    simp [armEmpiricalMean, Set.toFinset_ofPred, Finset.sum_filter]
  rw [heq]
  apply Measurable.div _ ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
    (measurable_armPullCount_local i))
  apply Finset.measurable_sum
  intro t ht
  have hm : Measurable (fun h : BanditHistory k n => (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const)
    (measurable_snd.comp (measurable_pi_apply t)) measurable_const

end BanditAlgorithm

theorem solution {k n : ℕ} (i : Fin k) :
    Measurable (BanditAlgorithm.klucbIndex (n := n) i) := by
  have hp := BanditAlgorithm.measurable_armEmpiricalMean_local (n := n) i
  have hc : Measurable (fun h : BanditAlgorithm.BanditHistory k n =>
      Real.log (BanditAlgorithm.klucbExploration (n + 1)) /
        BanditAlgorithm.armPullCount i h) :=
    measurable_const.div ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (BanditAlgorithm.measurable_armPullCount_local i))
  exact KLUCBMeasurability.measurable_scalarIndex.comp (hp.prodMk hc)

#check @solution
#print axioms solution
