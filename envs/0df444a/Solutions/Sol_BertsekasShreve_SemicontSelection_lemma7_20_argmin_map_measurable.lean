-- Prove2me | solution 1 for BertsekasShreve.SemicontSelection.lemma7_20_argmin_map_measurable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:07:29.942986+00:00
-- url     : https://prove2.me/submissions/7d228c5b-cfe7-4bd9-a24b-b5f3bfe699cd

import Mathlib



namespace BertsekasShreve.SemicontSelection

open TopologicalSpace Filter Topology Metric Set
open scoped ENNReal

theorem l720_infK {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X × Y → EReal) (hf : LowerSemicontinuous f) (K : Set Y) (hK : IsCompact K) :
    LowerSemicontinuous (fun x => ⨅ y ∈ K, f (x, y)) := by
  intro x0 c hc
  obtain ⟨c', hcc', hc'⟩ := exists_between hc
  have hP : ∀ y ∈ K, ∀ᶠ z : X × Y in 𝓝 (x0, y), c' < f (z.1, z.2) := fun y hy =>
    hf (x0, y) c' (lt_of_lt_of_le hc' (iInf₂_le y hy))
  have := hK.eventually_forall_of_forall_eventually (P := fun x y => c' < f (x, y)) hP
  filter_upwards [this] with x hx
  exact lt_of_lt_of_le hcc' (le_iInf₂ fun y hy => (hx y hy).le)

theorem l720_core {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (f : X × Y → EReal) (hf : LowerSemicontinuous f) :
    ∃ F : X → Closeds Y, (∀ x, (F x : Set Y) = {y | f (x, y) ≤ ⨅ y', f (x, y')}) ∧
      @Measurable _ _ (borel X) (borel (Closeds Y)) F := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace (Closeds Y) := borel _
  haveI : BorelSpace (Closeds Y) := ⟨rfl⟩
  have hsec : ∀ x, LowerSemicontinuous (fun y => f (x, y)) := fun x y c hc =>
    ((by fun_prop : Continuous fun y : Y => (x, y)).tendsto y).eventually (hf (x, y) c hc)
  let fs : X → EReal := fun x => ⨅ y', f (x, y')
  have hfs : LowerSemicontinuous fs := by
    have := l720_infK f hf univ isCompact_univ
    simpa only [mem_univ, iInf_pos] using this
  let F : X → Closeds Y := fun x => ⟨{y | f (x, y) ≤ fs x}, (hsec x).isClosed_preimage (fs x)⟩
  refine ⟨F, fun x => rfl, ?_⟩
  have hitK : ∀ K : Set Y, IsClosed K → MeasurableSet {x | ∃ y ∈ (F x : Set Y), y ∈ K} := by
    intro K hK
    have hKc := hK.isCompact
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    have : {x | ∃ y ∈ (F x : Set Y), y ∈ K} = {x | (⨅ y ∈ K, f (x, y)) ≤ fs x} := by
      ext x; constructor
      · rintro ⟨y, hy, hyK⟩; exact le_trans (iInf₂_le (f := fun y _ => f (x, y)) y hyK) (show f (x, y) ≤ fs x from hy)
      · intro hle
        obtain ⟨a, haK, hmin⟩ := ((hsec x).lowerSemicontinuousOn K).exists_isMinOn hne hKc
        refine ⟨a, ?_, haK⟩
        show f (x, a) ≤ fs x
        exact le_trans (le_iInf₂ (f := fun y _ => f (x, y)) fun y hy => hmin hy) (show (⨅ y ∈ K, f (x, y)) ≤ fs x from hle)
    rw [this]
    exact measurableSet_le (l720_infK f hf K hKc).measurable hfs.measurable
  have hitO : ∀ O : Set Y, IsOpen O → MeasurableSet {x | ∃ y ∈ (F x : Set Y), y ∈ O} := by
    intro O hO
    obtain ⟨T, hTo, hTc, hTeq⟩ := hO.isClosed_compl.isGδ
    have hO' : O = ⋃ t ∈ T, tᶜ := by
      rw [← compl_compl O, hTeq, compl_sInter, sUnion_image]
    have : {x | ∃ y ∈ (F x : Set Y), y ∈ O} = ⋃ t ∈ T, {x | ∃ y ∈ (F x : Set Y), y ∈ tᶜ} := by
      ext x
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · rintro ⟨y, hy, hyO⟩
        rw [hO'] at hyO
        simp only [mem_iUnion] at hyO
        obtain ⟨t, ht, hyt⟩ := hyO
        exact ⟨t, ht, y, hy, hyt⟩
      · rintro ⟨t, ht, y, hy, hyt⟩
        refine ⟨y, hy, ?_⟩
        rw [hO']; simp only [mem_iUnion]; exact ⟨t, ht, hyt⟩
    rw [this]
    exact MeasurableSet.biUnion hTc (fun t ht => hitK _ (hTo t ht).isClosed_compl)
  have hinfm : ∀ c : Y, Measurable (fun x => infEDist c (F x : Set Y)) := by
    intro c
    apply measurable_of_Iio
    intro s
    have : (fun x => infEDist c (F x : Set Y)) ⁻¹' Iio s =
        {x | ∃ y ∈ (F x : Set Y), y ∈ EMetric.ball c s} := by
      ext x
      simp only [mem_preimage, mem_Iio, infEDist_lt_iff, mem_setOf_eq]
      constructor <;> rintro ⟨y, hy, h⟩ <;> refine ⟨y, hy, ?_⟩
      · show edist y c < s
        rw [edist_comm]; exact h
      · have h' : edist y c < s := h
        rw [edist_comm] at h'; exact h'
    rw [this]
    exact hitO _ EMetric.isOpen_ball
  have hdist : ∀ C : Closeds Y, Measurable (fun x => edist (F x) C) := by
    intro C
    simp only [Closeds.edist_eq, hausdorffEDist_def]
    apply Measurable.sup
    · apply measurable_of_Iic
      intro r
      have : (fun x => ⨆ y ∈ (F x : Set Y), infEDist y (C : Set Y)) ⁻¹' Iic r =
          {x | ∃ y ∈ (F x : Set Y), y ∈ {y | r < infEDist y (C : Set Y)}}ᶜ := by
        ext x
        simp only [mem_preimage, mem_Iic, iSup₂_le_iff, mem_compl_iff, mem_setOf_eq, not_exists,
          not_and, not_lt]
      rw [this]
      exact (hitO _ (isOpen_lt continuous_const continuous_infEDist)).compl
    · obtain ⟨D, hDC, hDc, hCD⟩ :=
        (IsSeparable.of_separableSpace (C : Set Y)).exists_countable_dense_subset
      have heq : (fun x => ⨆ c ∈ (C : Set Y), infEDist c (F x : Set Y)) =
          fun x => ⨆ c ∈ D, infEDist c (F x : Set Y) := by
        funext x
        apply le_antisymm
        · apply iSup₂_le
          intro c hc
          have hcl : IsClosed {c | infEDist c (F x : Set Y) ≤ ⨆ d ∈ D, infEDist d (F x : Set Y)} :=
            isClosed_le continuous_infEDist continuous_const
          have hsub : D ⊆ {c | infEDist c (F x : Set Y) ≤ ⨆ d ∈ D, infEDist d (F x : Set Y)} :=
            fun d hd => le_iSup₂ (f := fun d _ => infEDist d (F x : Set Y)) d hd
          exact hcl.closure_subset_iff.mpr hsub (hCD hc)
        · exact iSup₂_le fun d hd => le_iSup₂ (f := fun c _ => infEDist c (F x : Set Y)) d (hDC hd)
      rw [heq]
      exact Measurable.biSup D hDc (fun c _ => hinfm c)
  apply measurable_of_isOpen
  intro U hU
  have hball : ∀ A ∈ U, ∃ ε > 0, EMetric.ball A ε ⊆ U := EMetric.isOpen_iff.mp hU
  let ι := {p : Closeds Y × ℝ≥0∞ // EMetric.ball p.1 p.2 ⊆ U}
  obtain ⟨T, hTc, hTeq⟩ := isOpen_iUnion_countable (fun i : ι => EMetric.ball i.1.1 i.1.2)
    (fun i => EMetric.isOpen_ball)
  have hU' : U = ⋃ i : ι, EMetric.ball i.1.1 i.1.2 := by
    ext A; constructor
    · intro hA
      obtain ⟨ε, hε, hb⟩ := hball A hA
      exact mem_iUnion.mpr ⟨⟨(A, ε), hb⟩, EMetric.mem_ball_self hε⟩
    · intro hA
      obtain ⟨i, hi⟩ := mem_iUnion.mp hA
      exact i.2 hi
  rw [hU', ← hTeq, preimage_iUnion₂]
  exact MeasurableSet.biUnion hTc (fun i _ => measurableSet_lt (hdist i.1.1) measurable_const)

end BertsekasShreve.SemicontSelection

open BertsekasShreve.SemicontSelection
open TopologicalSpace BertsekasShreve.SemicontSelection

theorem solution {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (f : X × Y → EReal) (hf : LowerSemicontinuous f) :
    ∃ F : X → Closeds Y, (∀ x, (F x : Set Y) = {y | f (x, y) ≤ ⨅ y', f (x, y')}) ∧
      @Measurable _ _ (borel X) (borel (Closeds Y)) F := by
  exact l720_core f hf
