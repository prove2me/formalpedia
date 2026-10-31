-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_strongAdapted_leftContinuous_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:09:57.564224+00:00
-- url     : https://prove2.me/submissions/ddae31f9-5b71-450d-858f-bc0ceff8dcb9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Order TopologicalSpace MeasureTheory
open scoped MeasureTheory NNReal ENNReal Topology
variable {Ω ι : Type*} {m : MeasurableSpace Ω}
variable [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι m}
private def wave3_04_roundDown (s : Finset ι) (i : ι) :=
  (insert ⊥ {j ∈ s | j < i}).max' (by simp)
private lemma wave3_04_roundDown_bot {s : Finset ι} :
    wave3_04_roundDown s ⊥ = ⊥ :=
  eq_bot_iff.mpr <| Finset.max'_le _ _ _ (by simp)

private lemma wave3_04_roundDown_lt_of_ne_bot
    {s : Finset ι} {i : ι} (h : i ≠ ⊥) :
    wave3_04_roundDown s i < i := by
  apply lt_of_le_of_ne
  · exact Finset.max'_le _ _ _ fun _ _ ↦ by grind
  · contrapose! h
    simp [wave3_04_roundDown, Finset.max'_eq_iff] at h
    grind

private lemma wave3_04_roundDown_le_of_subset
    {s t : Finset ι} {i : ι} (h : s ⊆ t) :
    wave3_04_roundDown s i ≤ wave3_04_roundDown t i :=
  Finset.max'_le _ _ _ <| fun _ _ ↦ by apply Finset.le_max'; grind

private lemma wave3_04_predictable_univ_prod
    {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) :
    MeasurableSet[𝓕.predictable] (Set.univ ×ˢ s) := by
  have hbot := measurableSet_predictable_singleton_bot_prod hs
  have hpos := measurableSet_predictable_Ioi_prod hs
  have heq : (Set.univ ×ˢ s : Set (ι × Ω)) =
      ({⊥} ×ˢ s) ∪ (Set.Ioi ⊥ ×ˢ s) := by
    ext ⟨i, ω⟩
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_union,
      Set.mem_singleton_iff, Set.mem_Ioi]
    grind [bot_le]
  rw [heq]
  exact hbot.union hpos

private lemma wave3_04_predictable_Iic_prod
    (t : ι) {s : Set Ω} (hs : MeasurableSet[𝓕 ⊥] s) :
    MeasurableSet[𝓕.predictable] (Set.Iic t ×ˢ s) := by
  have h := wave3_04_predictable_univ_prod hs
  have hp := measurableSet_predictable_Ioi_prod (i := t) (𝓕.mono bot_le _ hs)
  have heq : (Set.Iic t ×ˢ s : Set (ι × Ω)) =
      (Set.univ ×ˢ s) \ (Set.Ioi t ×ˢ s) := by
    ext ⟨i, ω⟩
    simp [Set.mem_prod]
    grind
  rw [heq]
  exact h.diff hp
variable {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
variable {X : ι → Ω → β}
private lemma wave3_04_stronglyPredictable_roundDown
    {times : Finset ι} (h_adap : StronglyAdapted 𝓕 X) :
    IsStronglyPredictable 𝓕
      (fun i ω ↦ X (wave3_04_roundDown times i) ω) := by
  let : MeasurableSpace (ι × Ω) := 𝓕.predictable
  let X_ap n i : @SimpleFunc Ω (𝓕 i) β := (h_adap i).approx n
  let Y s (x : ι × Ω) : β :=
    X (wave3_04_roundDown s x.1) x.2
  let Y_ap n s (x : ι × Ω) : β :=
    X_ap n (wave3_04_roundDown s x.1) x.2
  apply stronglyMeasurable_of_tendsto (u := atTop)
    (f := fun n x ↦ Y_ap n times x)
  · refine fun n ↦ SimpleFunc.mk (Y_ap n times) (fun b ↦ ?_) ?_ |>.stronglyMeasurable
    · refine times.induction_on_max ?_ ?_
      · apply MeasurableSet.congr
          (s := Set.univ ×ˢ (X_ap n ⊥ ⁻¹' {b})) _ (by aesop)
        exact wave3_04_predictable_univ_prod (by measurability)
      refine fun t times ht_max hm ↦ MeasurableSet.congr
        (s := ((Y_ap n times ⁻¹' {b}) ∩ (Set.Iic t ×ˢ Set.univ)) ∪
          (Set.Ioi t) ×ˢ (X_ap n t ⁻¹' {b})) ?_ ?_
      · apply MeasurableSet.union
        · exact hm.inter (wave3_04_predictable_Iic_prod t .univ)
        · exact measurableSet_predictable_Ioi_prod (by measurability)
      · ext ⟨i, ω⟩
        simp_rw [Y_ap, Set.mem_preimage]
        by_cases! hi : i ≤ t
        · have : wave3_04_roundDown (insert t times) i =
            wave3_04_roundDown times i := by
            rw [wave3_04_roundDown]; congr 2; grind
          simp
          grind
        · have : wave3_04_roundDown (insert t times) i = t := by
            rw [wave3_04_roundDown, Finset.max'_eq_iff]
            grind
          simp
          grind
    · apply Set.Finite.subset
        (s := ⋃ i ∈ Set.range (wave3_04_roundDown times),
          Set.range (X_ap n i)) _
        <| fun _ _ ↦ by simp; grind
      apply Set.Finite.biUnion _ <| fun i _ ↦ @(X_ap n i).finite_range
      refine Set.Finite.subset (s := insert ⊥ times) (by simp) fun i hi ↦ ?_
      obtain ⟨j, rfl⟩ := Set.mem_range.mp hi
      rw [← Finset.coe_insert, Finset.mem_coe]
      apply Finset.mem_of_subset
        (s₁ := insert ⊥ {s ∈ times | s < j}) (by simp)
      exact Finset.max'_mem _ _
  · simpa [Y_ap, tendsto_pi_nhds] using
      fun _ ↦ by apply StronglyMeasurable.tendsto_approx
variable [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
/-- An adapted left-continuous process is predictable on a densely ordered,
separable index set with a bottom element. Port of Mathlib PR #44961. -/
theorem solution
    {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [SeparableSpace ι]
    {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    {𝓕 : Filtration ι m} {X : ι → Ω → β}
    (h_adap : StronglyAdapted 𝓕 X)
    (h_cont : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Iic t) t) :
    IsStronglyPredictable 𝓕 X := by
  obtain ⟨d, hd_count, hd_dense⟩ := exists_countable_dense ι
  let times n :=
    Finset.image (Set.enumerateCountable hd_count ⊥) (Finset.range n)
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun n x ↦ X (wave3_04_roundDown (times n) x.1) x.2)
  · exact fun _ ↦ wave3_04_stronglyPredictable_roundDown (by grind)
  rw [tendsto_pi_nhds]
  intro ⟨i, ω⟩
  apply (h_cont ω i).tendsto.comp
  simp_rw [tendsto_nhdsWithin_iff]
  by_cases! hi_bot : i = ⊥
  · simp [hi_bot, wave3_04_roundDown_bot]
  refine ⟨?_, .of_forall <| fun _ ↦ le_of_lt <|
    wave3_04_roundDown_lt_of_ne_bot hi_bot⟩
  apply tendsto_atTop_isLUB
    (fun _ _ _ ↦ wave3_04_roundDown_le_of_subset <| by grind)
  apply (isLUB_congr _).mp (isLUB_Iio (a := i))
  ext j
  simp_rw [mem_upperBounds, Set.mem_Iio]
  constructor
  · refine fun hj k hk ↦ hj _ ?_
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hk
    exact wave3_04_roundDown_lt_of_ne_bot hi_bot
  · intro hj k hk
    obtain ⟨r, hr_mem, hr_lt⟩ := hd_dense.exists_between hk
    obtain ⟨n, h_rn⟩ := Set.mem_range.mp <|
      Set.subset_range_enumerate hd_count ⊥ hr_mem
    trans wave3_04_roundDown (times (n + 1)) i
    · exact hr_lt.1.le.trans <| Finset.le_max' _ _ (by grind)
    · exact hj _ (by grind)

