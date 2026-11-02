-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_5_16
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T05:27:06.874522+00:00
-- url     : https://prove2.me/submissions/85c3c175-dfc1-48f7-bf47-da92e6fc59d8

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_EMS

/- Source: Work.Gelfand516.Lifting.SetDensity; SHA256 f8b770de52c651a448ce4aa81b7a0d4abf9747a4973e05b5c447f4903b2ee7f6. -/
section Gelfand516Source0

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X}

/-- A partial lower density on a sub-sigma-algebra, in the set formulation of
Fremlin 341C–D. The output remains measurable for that sub-sigma-algebra. -/
structure SetDensity (m : MeasurableSpace X) (μ : @Measure X m₀) where
  toFun : Set X → Set X
  measurable : ∀ s, MeasurableSet[m] s → MeasurableSet[m] (toFun s)
  ae_rep : ∀ s, MeasurableSet[m] s → ∀ᵐ x ∂μ, x ∈ toFun s ↔ x ∈ s
  congr : ∀ s t, MeasurableSet[m] s → MeasurableSet[m] t →
    (∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) → toFun s = toFun t
  empty : toFun ∅ = ∅
  inter : ∀ s t, MeasurableSet[m] s → MeasurableSet[m] t →
    toFun (s ∩ t) = toFun s ∩ toFun t

namespace SetDensity
variable {m : MeasurableSpace X} {μ : @Measure X m₀} (ρ : @SetDensity X m₀ m μ)

theorem mono_ae {s t : Set X} (hs : MeasurableSet[m] s) (ht : MeasurableSet[m] t)
    (h : ∀ᵐ x ∂μ, x ∈ s → x ∈ t) : ρ.toFun s ⊆ ρ.toFun t := by
  have he : ρ.toFun (s ∩ t) = ρ.toFun s := by
    apply ρ.congr _ _ (hs.inter ht) hs
    filter_upwards [h] with x hx
    exact ⟨fun hst => hst.1, fun hxs => ⟨hxs, hx hxs⟩⟩
  rw [ρ.inter s t hs ht] at he
  exact inter_eq_left.mp he

theorem mono {s t : Set X} (hs : MeasurableSet[m] s) (ht : MeasurableSet[m] t)
    (h : s ⊆ t) : ρ.toFun s ⊆ ρ.toFun t :=
  ρ.mono_ae hs ht (Eventually.of_forall h)

theorem null {s : Set X} (hs : MeasurableSet[m] s)
    (h : ∀ᵐ x ∂μ, x ∉ s) : ρ.toFun s = ∅ := by
  rw [← ρ.empty]
  apply ρ.congr s ∅ hs MeasurableSet.empty
  filter_upwards [h] with x hx
  simp only [mem_empty_iff_false, iff_false]
  exact hx

end SetDensity
end Gelfand516Lifting
end
end Gelfand516Source0

/- Source: Work.Gelfand516.Lifting.RelativeHull; SHA256 47781702fda2dc6e68af29a71f7c31840dc8250aa241f08b1cd824a48b0b2b0f. -/
section Gelfand516Source1

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)
  (m : MeasurableSpace X) (hm : m ≤ m₀)

/-- Every ambient null set belongs to the intermediate sigma-algebra. This
is the saturation invariant used throughout Fremlin's lower-density induction. -/
def ContainsNullSets : Prop := ∀ s : Set X, μ s = 0 → MeasurableSet[m] s

/-- A relative measurable envelope in the intermediate sigma-algebra. -/
def relativeHull (s : Set X) : Set X := @toMeasurable X m (μ.trim hm) s

theorem relativeHull_measurable (s : Set X) : MeasurableSet[m] (relativeHull μ m hm s) :=
  @measurableSet_toMeasurable X m (μ.trim hm) s

theorem subset_relativeHull (s : Set X) : s ⊆ relativeHull μ m hm s :=
  @subset_toMeasurable X m (μ.trim hm) s

variable [IsFiniteMeasure μ]

/-- Relative envelopes have the least-upper-bound property modulo the ambient
null ideal, including upper bounds that contain the original set only a.e. -/
theorem relativeHull_minimal (hnull : ContainsNullSets μ m) {s a : Set X}
    (ha : MeasurableSet[m] a) (hsa : μ (s \ a) = 0) :
    μ (relativeHull μ m hm s \ a) = 0 := by
  have htrim : (μ.trim hm) (s \ a) = 0 := by
    rw [trim_measurableSet_eq hm (hnull (s \ a) hsa), hsa]
  apply measure_eq_zero_of_trim_eq_zero hm
  change (μ.trim hm) (@toMeasurable X m (μ.trim hm) s ∩ aᶜ) = 0
  rw [Measure.measure_toMeasurable_inter ha.compl (measure_ne_top (μ.trim hm) s)]
  exact htrim

theorem relativeHull_minimal_ae (hnull : ContainsNullSets μ m) {s a : Set X}
    (ha : MeasurableSet[m] a) (hsa : ∀ᵐ x ∂μ, x ∈ s → x ∈ a) :
    ∀ᵐ x ∂μ, x ∈ relativeHull μ m hm s → x ∈ a :=
  ae_le_set.mpr (relativeHull_minimal μ m hm hnull ha (ae_le_set.mp hsa))

end Gelfand516Lifting
end
end Gelfand516Source1

/- Source: Work.Gelfand516.Lifting.InitialDensity; SHA256 35713213a7c1c18ea108108e6bd7dc01e886f9a4e302e67f4cb9819c86892396. -/
section Gelfand516Source2

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)

/-- The saturated starting sigma-algebra consists of null and conull sets. -/
def nullConullSigma : MeasurableSpace X where
  MeasurableSet' s := μ s = 0 ∨ μ sᶜ = 0
  measurableSet_empty := Or.inl (measure_empty)
  measurableSet_compl := by
    intro s hs
    simpa only [compl_compl] using hs.symm
  measurableSet_iUnion := by
    intro s hs
    by_cases h : ∀ n, μ (s n) = 0
    · exact Or.inl (measure_iUnion_null h)
    · push_neg at h
      obtain ⟨n, hn⟩ := h
      apply Or.inr
      apply measure_mono_null (compl_subset_compl.mpr (subset_iUnion s n))
      exact (hs n).resolve_left hn

theorem nullConullSigma_le
    (hcomplete : ∀ s : Set X, μ s = 0 → MeasurableSet[m₀] s) : nullConullSigma μ ≤ m₀ := by
  intro s hs
  rcases hs with hs | hs
  · exact hcomplete s hs
  · simpa only [compl_compl] using (hcomplete sᶜ hs).compl

theorem nullConullSigma_containsNullSets : ContainsNullSets μ (nullConullSigma μ) :=
  fun _ hs => Or.inl hs

def initialDensitySet (s : Set X) : Set X := if μ s = 0 then ∅ else univ

theorem initialDensitySet_measurable (s : Set X) :
    MeasurableSet[nullConullSigma μ] (initialDensitySet μ s) := by
  unfold initialDensitySet
  split_ifs
  · exact @MeasurableSet.empty X (nullConullSigma μ)
  · exact @MeasurableSet.univ X (nullConullSigma μ)

theorem initialDensitySet_ae_rep {s : Set X} (hs : MeasurableSet[nullConullSigma μ] s) :
    ∀ᵐ x ∂μ, x ∈ initialDensitySet μ s ↔ x ∈ s := by
  by_cases hn : μ s = 0
  · filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hn] with x hx
    simp only [initialDensitySet, if_pos hn, mem_empty_iff_false, false_iff]
    exact hx
  · have hc : μ sᶜ = 0 := hs.resolve_left hn
    have hae : ∀ᵐ x ∂μ, x ∈ s := by
      simpa only [mem_compl_iff, not_not] using (measure_eq_zero_iff_ae_notMem).mp hc
    filter_upwards [hae] with x hx
    simp only [initialDensitySet, if_neg hn, mem_univ, true_iff]
    exact hx

theorem initialDensitySet_congr {s t : Set X} (h : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) :
    initialDensitySet μ s = initialDensitySet μ t := by
  have he : μ s = μ t := measure_congr (h.mono (fun _ hx => propext hx))
  simp only [initialDensitySet, he]

theorem initialDensitySet_inter (hnonnull : μ univ ≠ 0) {s t : Set X}
    (hs : MeasurableSet[nullConullSigma μ] s) (ht : MeasurableSet[nullConullSigma μ] t) :
    initialDensitySet μ (s ∩ t) = initialDensitySet μ s ∩ initialDensitySet μ t := by
  by_cases hsn : μ s = 0
  · have hst : μ (s ∩ t) = 0 := measure_mono_null inter_subset_left hsn
    simp [initialDensitySet, hsn, hst]
  by_cases htn : μ t = 0
  · have hst : μ (s ∩ t) = 0 := measure_mono_null inter_subset_right htn
    simp [initialDensitySet, htn, hst]
  have hsc : μ sᶜ = 0 := hs.resolve_left hsn
  have htc : μ tᶜ = 0 := ht.resolve_left htn
  have hstc : μ (s ∩ t)ᶜ = 0 := by
    rw [compl_inter]
    exact measure_union_null hsc htc
  have hstn : μ (s ∩ t) ≠ 0 := by
    intro hzero
    have hz := measure_union_null hzero hstc
    rw [union_compl_self] at hz
    exact hnonnull hz
  simp [initialDensitySet, hsn, htn, hstn]

/-- The initial lower density sends null sets to the empty set and conull sets
to the whole space. Nonzero total mass keeps these cases disjoint. -/
def initialDensity (hnonnull : μ univ ≠ 0) : @SetDensity X m₀ (nullConullSigma μ) μ where
  toFun := initialDensitySet μ
  measurable := fun s _ => initialDensitySet_measurable μ s
  ae_rep := fun _ hs => initialDensitySet_ae_rep μ hs
  congr := fun _ _ _ _ h => initialDensitySet_congr μ h
  empty := by simp [initialDensitySet]
  inter := fun _ _ hs ht => initialDensitySet_inter μ hnonnull hs ht

end Gelfand516Lifting
end
end Gelfand516Source2

/- Source: Work.Gelfand516.Lifting.TwoCell; SHA256 1e110b7ecb001b7d06442cceedb6e8b6cf4c6f93f8682602eef384c069b28515. -/
section Gelfand516Source3

set_option autoImplicit false
noncomputable section
open Set MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u}

def splice (s a b : Set X) : Set X := (a ∩ s) ∪ (b \ s)

lemma splice_self (s a : Set X) : splice s a a = a := by
  ext x
  simp only [splice, mem_union, mem_inter_iff, mem_sdiff]
  tauto

lemma splice_flip (s a b : Set X) : splice sᶜ b a = splice s a b := by
  ext x
  simp only [splice, mem_union, mem_inter_iff, mem_sdiff, mem_compl_iff]
  tauto

lemma splice_compl (s a b : Set X) : (splice s a b)ᶜ = splice s aᶜ bᶜ := by
  ext x
  simp only [splice, mem_compl_iff, mem_union, mem_inter_iff, mem_sdiff]
  tauto

lemma splice_inter (s a b c d : Set X) :
    splice s a b ∩ splice s c d = splice s (a ∩ c) (b ∩ d) := by
  ext x
  simp only [splice, mem_union, mem_inter_iff, mem_sdiff]
  tauto

lemma splice_iUnion (s : Set X) (a b : ℕ → Set X) :
    (⋃ n, splice s (a n) (b n)) = splice s (⋃ n, a n) (⋃ n, b n) := by
  ext x
  simp only [splice, mem_iUnion, mem_union, mem_inter_iff, mem_sdiff]
  aesop

/-- Adjoining one set to a sigma-algebra has a two-cell normal form. -/
def twoCellSigma (m : MeasurableSpace X) (s : Set X) : MeasurableSpace X where
  MeasurableSet' t := ∃ a b : Set X, MeasurableSet[m] a ∧ MeasurableSet[m] b ∧
    t = splice s a b
  measurableSet_empty := ⟨∅, ∅, MeasurableSet.empty, MeasurableSet.empty, by
    ext x; simp [splice]⟩
  measurableSet_compl := by
    rintro t ⟨a, b, ha, hb, rfl⟩
    exact ⟨aᶜ, bᶜ, ha.compl, hb.compl, splice_compl s a b⟩
  measurableSet_iUnion := by
    intro t ht
    choose a b ha hb he using ht
    refine ⟨⋃ n, a n, ⋃ n, b n, MeasurableSet.iUnion ha, MeasurableSet.iUnion hb, ?_⟩
    simp_rw [he]
    exact splice_iUnion s a b

theorem measurableSet_twoCellSigma_iff (m : MeasurableSpace X) (s t : Set X) :
    MeasurableSet[twoCellSigma m s] t ↔
      ∃ a b : Set X, MeasurableSet[m] a ∧ MeasurableSet[m] b ∧ t = splice s a b := Iff.rfl

theorem le_twoCellSigma (m : MeasurableSpace X) (s : Set X) : m ≤ twoCellSigma m s := by
  intro a ha
  exact ⟨a, a, ha, ha, (splice_self s a).symm⟩

theorem measurableSet_twoCellSigma (m : MeasurableSpace X) (s : Set X) :
    MeasurableSet[twoCellSigma m s] s := by
  refine ⟨univ, ∅, MeasurableSet.univ, MeasurableSet.empty, ?_⟩
  ext x
  simp [splice]

theorem twoCellSigma_le {m m₀ : MeasurableSpace X} (hm : m ≤ m₀)
    {s : Set X} (hs : MeasurableSet[m₀] s) : twoCellSigma m s ≤ m₀ := by
  rintro t ⟨a, b, ha, hb, rfl⟩
  exact ((hm a ha).inter hs).union ((hm b hb).diff hs)

end Gelfand516Lifting
end
end Gelfand516Source3

/- Source: Work.Gelfand516.Lifting.SuccessorCandidate; SHA256 14e124094b481bf96f779ba1b364d681f1fb6510642bde8fbced5c1a574960f2. -/
section Gelfand516Source4

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)
  [IsFiniteMeasure μ] (m : MeasurableSpace X) (hm : m ≤ m₀)
  (hnull : ContainsNullSets (m₀ := m₀) μ m) (ρ : @SetDensity X m₀ m μ)

lemma splice_measurable {s a b : Set X} (hs : MeasurableSet[m] s)
    (ha : MeasurableSet[m] a) (hb : MeasurableSet[m] b) : MeasurableSet[m] (splice s a b) :=
  (ha.inter hs).union (hb.diff hs)

include hnull in
/-- Replacing the new cell by its relative measurable envelope preserves
almost-everywhere comparisons between two-cell representatives. -/
lemma splice_hull_mono_ae {s a b c d : Set X}
    (ha : MeasurableSet[m] a) (hc : MeasurableSet[m] c)
    (h : ∀ᵐ x ∂μ, x ∈ splice s a b → x ∈ splice s c d) :
    ∀ᵐ x ∂μ, x ∈ splice (relativeHull μ m hm s) a b →
      x ∈ splice (relativeHull μ m hm s) c d := by
  have hsa : ∀ᵐ x ∂μ, x ∈ s → x ∈ aᶜ ∪ c := by
    filter_upwards [h] with x hx hxs
    by_cases hxa : x ∈ a
    · right
      have hh := hx (Or.inl ⟨hxa, hxs⟩)
      rcases hh with hh | hh
      · exact hh.1
      · exact (hh.2 hxs).elim
    · exact Or.inl hxa
  have hv := relativeHull_minimal_ae μ m hm hnull (ha.compl.union hc) hsa
  filter_upwards [h, hv] with x hx hxv hxb
  by_cases hmem : x ∈ relativeHull μ m hm s
  · have hxa : x ∈ a := by
      rcases hxb with hh | hh
      · exact hh.1
      · exact (hh.2 hmem).elim
    have hxc : x ∈ c := (hxv hmem).resolve_left (fun hh => hh hxa)
    exact Or.inl ⟨hxc, hmem⟩
  · have hxs : x ∉ s := fun hs => hmem (subset_relativeHull μ m hm s hs)
    have hb : x ∈ b := by
      rcases hxb with hh | hh
      · exact (hmem hh.2).elim
      · exact hh.1
    have hd : x ∈ d := by
      rcases hx (Or.inr ⟨hb, hxs⟩) with hh | hh
      · exact (hxs hh.2).elim
      · exact hh.1
    exact Or.inr ⟨hd, hmem⟩

/-- The explicit successor-stage formula of Fremlin341F, before choosing
coordinates for each measurable set in the enlarged sigma-algebra. -/
def successorCandidate (s a b : Set X) : Set X :=
  splice s (ρ.toFun (splice (relativeHull μ m hm s) a b))
    (ρ.toFun (splice (relativeHull μ m hm sᶜ) b a))

include hnull in
theorem successorCandidate_mono_ae {s a b c d : Set X}
    (ha : MeasurableSet[m] a) (hb : MeasurableSet[m] b)
    (hc : MeasurableSet[m] c) (hd : MeasurableSet[m] d)
    (h : ∀ᵐ x ∂μ, x ∈ splice s a b → x ∈ splice s c d) :
    successorCandidate μ m hm ρ s a b ⊆ successorCandidate μ m hm ρ s c d := by
  have hv := relativeHull_measurable μ m hm s
  have hw := relativeHull_measurable μ m hm sᶜ
  have hpos := ρ.mono_ae (splice_measurable m hv ha hb) (splice_measurable m hv hc hd)
    (splice_hull_mono_ae μ m hm hnull ha hc h)
  have hflip : ∀ᵐ x ∂μ, x ∈ splice sᶜ b a → x ∈ splice sᶜ d c := by
    simpa only [splice_flip] using h
  have hneg := ρ.mono_ae (splice_measurable m hw hb ha) (splice_measurable m hw hd hc)
    (splice_hull_mono_ae μ m hm hnull hb hd hflip)
  intro x hx
  rcases hx with hh | hh
  · exact Or.inl ⟨hpos hh.1, hh.2⟩
  · exact Or.inr ⟨hneg hh.1, hh.2⟩

include hnull in
theorem successorCandidate_congr {s a b c d : Set X}
    (ha : MeasurableSet[m] a) (hb : MeasurableSet[m] b)
    (hc : MeasurableSet[m] c) (hd : MeasurableSet[m] d)
    (h : ∀ᵐ x ∂μ, x ∈ splice s a b ↔ x ∈ splice s c d) :
    successorCandidate μ m hm ρ s a b = successorCandidate μ m hm ρ s c d :=
  Subset.antisymm
    (successorCandidate_mono_ae μ m hm hnull ρ ha hb hc hd (h.mono (fun _ hx => hx.mp)))
    (successorCandidate_mono_ae μ m hm hnull ρ hc hd ha hb (h.mono (fun _ hx => hx.mpr)))

theorem successorCandidate_ae_rep {s a b : Set X}
    (ha : MeasurableSet[m] a) (hb : MeasurableSet[m] b) :
    ∀ᵐ x ∂μ, x ∈ successorCandidate μ m hm ρ s a b ↔ x ∈ splice s a b := by
  have hv := relativeHull_measurable μ m hm s
  have hw := relativeHull_measurable μ m hm sᶜ
  filter_upwards [ρ.ae_rep _ (splice_measurable m hv ha hb),
    ρ.ae_rep _ (splice_measurable m hw hb ha)] with x hx hy
  change ((x ∈ ρ.toFun (splice (relativeHull μ m hm s) a b) ∧ x ∈ s) ∨
    (x ∈ ρ.toFun (splice (relativeHull μ m hm sᶜ) b a) ∧ x ∉ s)) ↔ _
  rw [hx, hy]
  have hvs := subset_relativeHull μ m hm s
  have hws := subset_relativeHull μ m hm sᶜ
  by_cases hxs : x ∈ s
  · have hxv := hvs hxs
    simp [splice, hxs, hxv]
  · have hxw := hws hxs
    simp [splice, hxs, hxw]

theorem successorCandidate_measurable {s a b : Set X}
    (ha : MeasurableSet[m] a) (hb : MeasurableSet[m] b) :
    MeasurableSet[twoCellSigma m s] (successorCandidate μ m hm ρ s a b) := by
  have hv := relativeHull_measurable μ m hm s
  have hw := relativeHull_measurable μ m hm sᶜ
  exact ⟨_, _, ρ.measurable _ (splice_measurable m hv ha hb),
    ρ.measurable _ (splice_measurable m hw hb ha), rfl⟩

theorem successorCandidate_diagonal (s a : Set X) :
    successorCandidate μ m hm ρ s a a = ρ.toFun a := by
  simp only [successorCandidate, splice_self]

theorem successorCandidate_empty (s : Set X) :
    successorCandidate μ m hm ρ s ∅ ∅ = ∅ := by
  rw [successorCandidate_diagonal, ρ.empty]

theorem successorCandidate_inter {s a b c d : Set X}
    (ha : MeasurableSet[m] a) (hb : MeasurableSet[m] b)
    (hc : MeasurableSet[m] c) (hd : MeasurableSet[m] d) :
    successorCandidate μ m hm ρ s (a ∩ c) (b ∩ d) =
      successorCandidate μ m hm ρ s a b ∩ successorCandidate μ m hm ρ s c d := by
  have hv := relativeHull_measurable μ m hm s
  have hw := relativeHull_measurable μ m hm sᶜ
  dsimp only [successorCandidate]
  rw [← splice_inter (relativeHull μ m hm s) a b c d,
    ρ.inter _ _ (splice_measurable m hv ha hb) (splice_measurable m hv hc hd),
    ← splice_inter (relativeHull μ m hm sᶜ) b a d c,
    ρ.inter _ _ (splice_measurable m hw hb ha) (splice_measurable m hw hd hc),
    ← splice_inter]

end Gelfand516Lifting
end
end Gelfand516Source4

/- Source: Work.Gelfand516.Lifting.SuccessorDensity; SHA256 2e93bd434d52e985aa00da8d8f816ad57e89229cd031e15b4161cd684f2796d5. -/
section Gelfand516Source5

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)
  [IsFiniteMeasure μ] (m : MeasurableSpace X) (hm : m ≤ m₀)
  (hnull : ContainsNullSets μ m) (ρ : @SetDensity X m₀ m μ)

include hm hnull in
/-- Fremlin341F in sigma-algebra form: adjoining one measurable set extends
the existing lower density exactly. Measurability of the new set in the
ambient space is needed only to keep the new domain below that ambient space. -/
theorem exists_successorDensity (s : Set X) :
    ∃ τ : @SetDensity X m₀ (twoCellSigma m s) μ,
      ∀ t : Set X, MeasurableSet[m] t → τ.toFun t = ρ.toFun t := by
  classical
  let D := {t : Set X // MeasurableSet[twoCellSigma m s] t}
  have hex (t : D) : ∃ a b : Set X, MeasurableSet[m] a ∧ MeasurableSet[m] b ∧
      t.val = splice s a b := t.property
  choose a b ha hb he using hex
  let f : Set X → Set X := fun t => if ht : MeasurableSet[twoCellSigma m s] t then
    successorCandidate μ m hm ρ s (a ⟨t, ht⟩) (b ⟨t, ht⟩) else ∅
  have hf (t : Set X) (ht : MeasurableSet[twoCellSigma m s] t)
      (c d : Set X) (hc : MeasurableSet[m] c) (hd : MeasurableSet[m] d)
      (hcd : t = splice s c d) : f t = successorCandidate μ m hm ρ s c d := by
    dsimp only [f]
    rw [dif_pos ht]
    apply successorCandidate_congr μ m hm hnull ρ (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) hc hd
    apply Eventually.of_forall
    intro x
    exact iff_of_eq (congrArg (fun z : Set X => x ∈ z) ((he ⟨t, ht⟩).symm.trans hcd))
  have hfmeas (t : Set X) (ht : MeasurableSet[twoCellSigma m s] t) :
      MeasurableSet[twoCellSigma m s] (f t) := by
    rw [hf t ht (a ⟨t, ht⟩) (b ⟨t, ht⟩) (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) (he ⟨t, ht⟩)]
    exact successorCandidate_measurable μ m hm ρ (ha ⟨t, ht⟩) (hb ⟨t, ht⟩)
  have hfrep (t : Set X) (ht : MeasurableSet[twoCellSigma m s] t) :
      ∀ᵐ x ∂μ, x ∈ f t ↔ x ∈ t := by
    rw [hf t ht (a ⟨t, ht⟩) (b ⟨t, ht⟩) (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) (he ⟨t, ht⟩)]
    filter_upwards [successorCandidate_ae_rep μ m hm ρ (ha ⟨t, ht⟩) (hb ⟨t, ht⟩)] with x hx
    exact hx.trans (iff_of_eq (congrArg (fun z : Set X => x ∈ z) (he ⟨t, ht⟩)).symm)
  have hfcongr (t u : Set X) (ht : MeasurableSet[twoCellSigma m s] t)
      (hu : MeasurableSet[twoCellSigma m s] u) (htu : ∀ᵐ x ∂μ, x ∈ t ↔ x ∈ u) :
      f t = f u := by
    rw [hf t ht (a ⟨t, ht⟩) (b ⟨t, ht⟩) (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) (he ⟨t, ht⟩),
      hf u hu (a ⟨u, hu⟩) (b ⟨u, hu⟩) (ha ⟨u, hu⟩) (hb ⟨u, hu⟩) (he ⟨u, hu⟩)]
    apply successorCandidate_congr μ m hm hnull ρ
      (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) (ha ⟨u, hu⟩) (hb ⟨u, hu⟩)
    filter_upwards [htu] with x hx
    exact (iff_of_eq (congrArg (fun z : Set X => x ∈ z) (he ⟨t, ht⟩))).symm.trans
      (hx.trans (iff_of_eq (congrArg (fun z : Set X => x ∈ z) (he ⟨u, hu⟩))))
  have hfempty : f ∅ = ∅ := by
    rw [hf ∅ (@MeasurableSet.empty X (twoCellSigma m s)) ∅ ∅
      (@MeasurableSet.empty X m) (@MeasurableSet.empty X m)
      (splice_self s ∅).symm, successorCandidate_empty]
  have hfinter (t u : Set X) (ht : MeasurableSet[twoCellSigma m s] t)
      (hu : MeasurableSet[twoCellSigma m s] u) : f (t ∩ u) = f t ∩ f u := by
    have hcoord : t ∩ u = splice s (a ⟨t, ht⟩ ∩ a ⟨u, hu⟩)
        (b ⟨t, ht⟩ ∩ b ⟨u, hu⟩) := by
      exact (congrArg₂ (fun v w : Set X => v ∩ w) (he ⟨t, ht⟩) (he ⟨u, hu⟩)).trans
        (splice_inter s _ _ _ _)
    rw [hf (t ∩ u) (ht.inter hu) _ _ ((ha ⟨t, ht⟩).inter (ha ⟨u, hu⟩))
      ((hb ⟨t, ht⟩).inter (hb ⟨u, hu⟩)) hcoord,
      hf t ht _ _ (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) (he ⟨t, ht⟩),
      hf u hu _ _ (ha ⟨u, hu⟩) (hb ⟨u, hu⟩) (he ⟨u, hu⟩)]
    exact successorCandidate_inter μ m hm ρ
      (ha ⟨t, ht⟩) (hb ⟨t, ht⟩) (ha ⟨u, hu⟩) (hb ⟨u, hu⟩)
  refine ⟨⟨f, hfmeas, hfrep, hfcongr, hfempty, hfinter⟩, ?_⟩
  intro t ht
  change f t = ρ.toFun t
  rw [hf t (le_twoCellSigma m s t ht) t t ht ht (splice_self s t).symm,
    successorCandidate_diagonal]

end Gelfand516Lifting
end
end Gelfand516Source5

/- Source: Work.Gelfand516.Lifting.CountableLimit; SHA256 3cc6e881f2b40e198b63f3893bb24ad929074486ba97d149096c93be9e027bc0. -/
section Gelfand516Source6

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ProbabilityTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} [m₀ : MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (ℱ : Filtration ℕ m₀) (ρ : ∀ n, SetDensity (ℱ n) μ)

def cutoff (k : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (k + 1)

lemma cutoff_lt_one (k : ℕ) : cutoff k < 1 := by
  dsimp [cutoff]
  have h : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  linarith

lemma cutoff_pos (k : ℕ) : 0 < cutoff k := by
  dsimp [cutoff]
  have h : (1 / 2 : ℝ) ^ (k + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num)
    (Nat.succ_ne_zero k)
  linarith

lemma cutoff_double (k : ℕ) : 2 * cutoff (k + 1) - 1 = cutoff k := by
  dsimp [cutoff]
  rw [show k + 1 + 1 = (k + 1) + 1 from rfl, pow_succ]
  ring

def ceIndicator (s : Set X) (n : ℕ) : X → ℝ := μ[s.indicator (fun _ => (1 : ℝ)) | ℱ n]

def thresholdSet (s : Set X) (k n : ℕ) : Set X :=
  {x | cutoff k ≤ ceIndicator μ ℱ s n x}

lemma thresholdSet_measurable (s : Set X) (k n : ℕ) :
    MeasurableSet[ℱ n] (thresholdSet μ ℱ s k n) :=
  measurableSet_le measurable_const stronglyMeasurable_condExp.measurable

def correctedThreshold (s : Set X) (k n : ℕ) : Set X :=
  (ρ n).toFun (thresholdSet μ ℱ s k n)

lemma correctedThreshold_measurable (s : Set X) (k n : ℕ) :
    MeasurableSet[ℱ n] (correctedThreshold μ ℱ ρ s k n) :=
  (ρ n).measurable _ (thresholdSet_measurable μ ℱ s k n)

/-- Fremlin 341G(d): all thresholds are eventually satisfied after applying
the density at each finite stage. -/
def countableDensitySet (s : Set X) : Set X :=
  ⋂ k : ℕ, ⋃ N : ℕ, ⋂ n ≥ N, correctedThreshold μ ℱ ρ s k n

lemma mem_countableDensitySet (s : Set X) (x : X) :
    x ∈ countableDensitySet μ ℱ ρ s ↔
      ∀ k, ∀ᶠ n : ℕ in atTop, x ∈ correctedThreshold μ ℱ ρ s k n := by
  simp only [countableDensitySet, mem_iInter, mem_iUnion, eventually_atTop]

lemma countableDensitySet_measurable (s : Set X) :
    MeasurableSet[⨆ n, ℱ n] (countableDensitySet μ ℱ ρ s) := by
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro N
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro _
  exact (le_iSup (fun n => ℱ n) n) _ (correctedThreshold_measurable μ ℱ ρ s k n)

lemma eventually_cutoffs_iff {g : ℕ → ℝ} {b : ℝ} (hb : b = 0 ∨ b = 1)
    (hg : Tendsto g atTop (𝓝 b)) :
    (∀ k, ∀ᶠ n : ℕ in atTop, cutoff k ≤ g n) ↔ b = 1 := by
  rcases hb with rfl | rfl
  · constructor
    · intro h
      have h0 := h 0
      have hlt : ∀ᶠ n : ℕ in atTop, g n < cutoff 0 :=
        hg.eventually (gt_mem_nhds (cutoff_pos 0))
      obtain ⟨n, hn, hnl⟩ := (h0.and hlt).exists
      exact (not_lt_of_ge hn hnl).elim
    · norm_num
  · constructor
    · intro _; rfl
    · intro _ k
      exact (hg.eventually (lt_mem_nhds (cutoff_lt_one k))).mono (fun _ h => h.le)

/-- The conditional-expectation limit represents the original measurable set
almost everywhere. This consumes the actual martingale convergence theorem. -/
theorem countableDensitySet_ae_rep {s : Set X} (hs : MeasurableSet[⨆ n, ℱ n] s) :
    ∀ᵐ x ∂μ, x ∈ countableDensitySet μ ℱ ρ s ↔ x ∈ s := by
  have hle : (⨆ n, ℱ n) ≤ m₀ := iSup_le ℱ.le
  have hi : Integrable (s.indicator (fun _ : X => (1 : ℝ))) μ :=
    (integrable_const 1).indicator (hle _ hs)
  have hm : StronglyMeasurable[⨆ n, ℱ n] (s.indicator (fun _ : X => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hs
  have ht := hi.tendsto_ae_condExp (ℱ := ℱ) hm
  have hrep : ∀ᵐ x ∂μ, ∀ k n, x ∈ correctedThreshold μ ℱ ρ s k n ↔
      x ∈ thresholdSet μ ℱ s k n := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro n
    exact (ρ n).ae_rep _ (thresholdSet_measurable μ ℱ s k n)
  filter_upwards [ht, hrep] with x hx hr
  rw [mem_countableDensitySet]
  simp_rw [hr]
  have hb : s.indicator (fun _ : X => (1 : ℝ)) x = 0 ∨
      s.indicator (fun _ : X => (1 : ℝ)) x = 1 := by
    by_cases hxs : x ∈ s <;> simp [hxs]
  have he := eventually_cutoffs_iff hb hx
  change (∀ k, ∀ᶠ n : ℕ in atTop, cutoff k ≤ ceIndicator μ ℱ s n x) ↔ x ∈ s
  exact he.trans (by by_cases hxs : x ∈ s <;> simp [hxs])

end Gelfand516Lifting
end
end Gelfand516Source6

/- Source: Work.Gelfand516.Lifting.CountableLimitLaws; SHA256 0084ef2f4675302142622a491e4c23c39b7731f708938fb7bb875a4f8512cb64. -/
section Gelfand516Source7

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ProbabilityTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} [m₀ : MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (ℱ : Filtration ℕ m₀) (ρ : ∀ n, SetDensity (ℱ n) μ)

lemma generated_le : (⨆ n, ℱ n) ≤ m₀ := iSup_le ℱ.le

lemma indicator_integrable {s : Set X} (hs : MeasurableSet[⨆ n, ℱ n] s) :
    Integrable (s.indicator (fun _ : X => (1 : ℝ))) μ :=
  (integrable_const 1).indicator (generated_le ℱ _ hs)

lemma correctedThreshold_mono_ae {s t : Set X}
    (hs : MeasurableSet[⨆ n, ℱ n] s) (ht : MeasurableSet[⨆ n, ℱ n] t)
    (hst : ∀ᵐ x ∂μ, x ∈ s → x ∈ t) (k n : ℕ) :
    correctedThreshold μ ℱ ρ s k n ⊆ correctedThreshold μ ℱ ρ t k n := by
  apply (ρ n).mono_ae (thresholdSet_measurable μ ℱ s k n)
    (thresholdSet_measurable μ ℱ t k n)
  have hle : s.indicator (fun _ : X => (1 : ℝ)) ≤ᵐ[μ]
      t.indicator (fun _ : X => (1 : ℝ)) := by
    filter_upwards [hst] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs, hx hxs]
    · by_cases hxt : x ∈ t <;> simp [hxs, hxt]
  have hc := condExp_mono (m := ℱ n) (indicator_integrable μ ℱ hs)
    (indicator_integrable μ ℱ ht) hle
  filter_upwards [hc] with x hx hxk
  exact hxk.trans hx

lemma countableDensitySet_mono_ae {s t : Set X}
    (hs : MeasurableSet[⨆ n, ℱ n] s) (ht : MeasurableSet[⨆ n, ℱ n] t)
    (hst : ∀ᵐ x ∂μ, x ∈ s → x ∈ t) :
    countableDensitySet μ ℱ ρ s ⊆ countableDensitySet μ ℱ ρ t := by
  intro x hx
  rw [mem_countableDensitySet] at hx ⊢
  intro k
  exact (hx k).mono (fun n hn => correctedThreshold_mono_ae μ ℱ ρ hs ht hst k n hn)

lemma countableDensitySet_congr {s t : Set X}
    (hs : MeasurableSet[⨆ n, ℱ n] s) (ht : MeasurableSet[⨆ n, ℱ n] t)
    (hst : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) :
    countableDensitySet μ ℱ ρ s = countableDensitySet μ ℱ ρ t := by
  apply Subset.antisymm
  · exact countableDensitySet_mono_ae μ ℱ ρ hs ht (hst.mono (fun _ h => h.mp))
  · exact countableDensitySet_mono_ae μ ℱ ρ ht hs (hst.mono (fun _ h => h.mpr))

lemma ceIndicator_inter_bound {s t : Set X}
    (hs : MeasurableSet[⨆ n, ℱ n] s) (ht : MeasurableSet[⨆ n, ℱ n] t) (n : ℕ) :
    ∀ᵐ x ∂μ, ceIndicator μ ℱ s n x + ceIndicator μ ℱ t n x - 1 ≤
      ceIndicator μ ℱ (s ∩ t) n x := by
  let f : X → ℝ := s.indicator (fun _ => 1)
  let g : X → ℝ := t.indicator (fun _ => 1)
  have hf : Integrable f μ := indicator_integrable μ ℱ hs
  have hg : Integrable g μ := indicator_integrable μ ℱ ht
  have hfg : f + g - (fun _ => 1) ≤ᵐ[μ] (s ∩ t).indicator (fun _ : X => (1 : ℝ)) := by
    apply Eventually.of_forall
    intro x
    by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
      simp [f, g, hxs, hxt]
  have hm := condExp_mono (m := ℱ n) ((hf.add hg).sub (integrable_const 1))
    (indicator_integrable μ ℱ (hs.inter ht)) hfg
  have hsub := condExp_sub (hf.add hg) (integrable_const (1 : ℝ)) (ℱ n)
  have hadd := condExp_add hf hg (ℱ n)
  filter_upwards [hm, hsub, hadd] with x hx hxs hxa
  rw [condExp_const (ℱ.le n) (1 : ℝ)] at hxs
  change μ[f + g - (fun _ => 1) | ℱ n] x ≤ ceIndicator μ ℱ (s ∩ t) n x at hx
  change μ[f + g - (fun _ => 1) | ℱ n] x = μ[f + g | ℱ n] x - 1 at hxs
  change μ[f + g | ℱ n] x = ceIndicator μ ℱ s n x + ceIndicator μ ℱ t n x at hxa
  rwa [hxs, hxa] at hx

lemma correctedThreshold_inter {s t : Set X}
    (hs : MeasurableSet[⨆ n, ℱ n] s) (ht : MeasurableSet[⨆ n, ℱ n] t) (k n : ℕ) :
    correctedThreshold μ ℱ ρ s (k + 1) n ∩ correctedThreshold μ ℱ ρ t (k + 1) n ⊆
      correctedThreshold μ ℱ ρ (s ∩ t) k n := by
  have h := (ρ n).mono_ae
    ((thresholdSet_measurable μ ℱ s (k + 1) n).inter
      (thresholdSet_measurable μ ℱ t (k + 1) n))
    (thresholdSet_measurable μ ℱ (s ∩ t) k n) (by
      filter_upwards [ceIndicator_inter_bound μ ℱ hs ht n] with x hx hxt
      have ha : cutoff (k + 1) ≤ ceIndicator μ ℱ s n x := hxt.1
      have hb : cutoff (k + 1) ≤ ceIndicator μ ℱ t n x := hxt.2
      change cutoff k ≤ ceIndicator μ ℱ (s ∩ t) n x
      have hc := cutoff_double k
      linarith)
  rwa [(ρ n).inter _ _ (thresholdSet_measurable μ ℱ s (k + 1) n)
    (thresholdSet_measurable μ ℱ t (k + 1) n)] at h

theorem countableDensitySet_inter {s t : Set X}
    (hs : MeasurableSet[⨆ n, ℱ n] s) (ht : MeasurableSet[⨆ n, ℱ n] t) :
    countableDensitySet μ ℱ ρ (s ∩ t) =
      countableDensitySet μ ℱ ρ s ∩ countableDensitySet μ ℱ ρ t := by
  apply Subset.antisymm
  · exact subset_inter
      (countableDensitySet_mono_ae μ ℱ ρ (hs.inter ht) hs
        (Eventually.of_forall (fun _ h => h.1)))
      (countableDensitySet_mono_ae μ ℱ ρ (hs.inter ht) ht
        (Eventually.of_forall (fun _ h => h.2)))
  · rintro x ⟨hxs, hxt⟩
    rw [mem_countableDensitySet] at hxs hxt ⊢
    intro k
    exact ((hxs (k + 1)).and (hxt (k + 1))).mono
      (fun n hn => correctedThreshold_inter μ ℱ ρ hs ht k n hn)

lemma thresholdSet_empty (k n : ℕ) : thresholdSet μ ℱ ∅ k n = ∅ := by
  have hz : ceIndicator μ ℱ ∅ n = (0 : X → ℝ) := by
    dsimp only [ceIndicator]
    rw [indicator_empty]
    change μ[(0 : X → ℝ) | ℱ n] = 0
    exact condExp_zero
  ext x
  simp only [thresholdSet, hz, Pi.zero_apply,
    mem_setOf_eq, mem_empty_iff_false, iff_false]
  exact not_le_of_gt (cutoff_pos k)

theorem countableDensitySet_empty : countableDensitySet μ ℱ ρ ∅ = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have h := ((mem_countableDensitySet μ ℱ ρ ∅ x).mp hx) 0
  obtain ⟨n, hn⟩ := h.exists
  change x ∈ (ρ n).toFun (thresholdSet μ ℱ ∅ 0 n) at hn
  rw [thresholdSet_empty, (ρ n).empty] at hn
  exact hn

/-- Fremlin 341G: the limit construction is a lower density on the sigma
algebra generated by the increasing finite stages. -/
def countableDensity : SetDensity (⨆ n, ℱ n) μ where
  toFun := countableDensitySet μ ℱ ρ
  measurable := fun s _ => countableDensitySet_measurable μ ℱ ρ s
  ae_rep := fun _ hs => countableDensitySet_ae_rep μ ℱ ρ hs
  congr := fun _ _ hs ht hst => countableDensitySet_congr μ ℱ ρ hs ht hst
  empty := countableDensitySet_empty μ ℱ ρ
  inter := fun _ _ hs ht => countableDensitySet_inter μ ℱ ρ hs ht

lemma thresholdSet_of_measurable {s : Set X} {N n : ℕ}
    (hs : MeasurableSet[ℱ N] s) (hNn : N ≤ n) (k : ℕ) :
    thresholdSet μ ℱ s k n = s := by
  have hsn : MeasurableSet[ℱ n] s := ℱ.mono hNn _ hs
  have hce : ceIndicator μ ℱ s n = s.indicator (fun _ : X => (1 : ℝ)) :=
    condExp_of_stronglyMeasurable (ℱ.le n) (stronglyMeasurable_const.indicator hsn)
      ((integrable_const 1).indicator (ℱ.le n _ hsn))
  ext x
  change cutoff k ≤ ceIndicator μ ℱ s n x ↔ x ∈ s
  rw [hce]
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, hx, iff_true]
    exact (cutoff_lt_one k).le
  · simp only [indicator_of_notMem hx, hx, iff_false]
    exact not_le_of_gt (cutoff_pos k)

/-- Compatibility of the earlier densities makes the countable limit an
exact extension, not merely an almost-everywhere extension. -/
theorem countableDensity_extends
    (hcompat : ∀ i j, i ≤ j → ∀ s, MeasurableSet[ℱ i] s →
      (ρ j).toFun s = (ρ i).toFun s) {s : Set X} (N : ℕ) (hs : MeasurableSet[ℱ N] s) :
    (countableDensity μ ℱ ρ).toFun s = (ρ N).toFun s := by
  ext x
  change x ∈ countableDensitySet μ ℱ ρ s ↔ x ∈ (ρ N).toFun s
  rw [mem_countableDensitySet]
  have he (k : ℕ) : (∀ᶠ n : ℕ in atTop, x ∈ correctedThreshold μ ℱ ρ s k n) ↔
      x ∈ (ρ N).toFun s := by
    have hseq : ∀ᶠ n : ℕ in atTop,
        (x ∈ correctedThreshold μ ℱ ρ s k n ↔ x ∈ (ρ N).toFun s) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      dsimp only [correctedThreshold]
      rw [thresholdSet_of_measurable μ ℱ hs hn k, hcompat N n hn s hs]
    exact (Filter.eventually_congr hseq).trans eventually_const
  simp_rw [he]
  simp

end Gelfand516Lifting
end
end Gelfand516Source7

/- Source: Work.Gelfand516.Lifting.PartialDensity; SHA256 6d8947788336399cee47bad5a41202a2ebb8af47bb11f44bf609f904da2934b1. -/
section Gelfand516Source8

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)

/-- A partial density with a saturated domain below the fixed ambient
sigma-algebra. Its values outside that domain play no role in the preorder. -/
structure PartialDensity where
  domain : MeasurableSpace X
  le_ambient : domain ≤ m₀
  contains_null : ContainsNullSets μ domain
  density : @SetDensity X m₀ domain μ

namespace PartialDensity

instance : Preorder (PartialDensity μ) where
  le p q := p.domain ≤ q.domain ∧ ∀ s : Set X, MeasurableSet[p.domain] s →
    q.density.toFun s = p.density.toFun s
  le_refl p := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans p q r hpq hqr := ⟨hpq.1.trans hqr.1, fun s hs =>
    (hqr.2 s (hpq.1 s hs)).trans (hpq.2 s hs)⟩

def initial (hcomplete : ∀ s : Set X, μ s = 0 → MeasurableSet[m₀] s)
    (hnonnull : μ univ ≠ 0) : PartialDensity μ where
  domain := nullConullSigma μ
  le_ambient := nullConullSigma_le μ hcomplete
  contains_null := nullConullSigma_containsNullSets μ
  density := initialDensity μ hnonnull

variable [IsFiniteMeasure μ]

theorem exists_adjoin (p : PartialDensity μ) (s : Set X) (hs : MeasurableSet[m₀] s) :
    ∃ q : PartialDensity μ, p ≤ q ∧ MeasurableSet[q.domain] s := by
  obtain ⟨τ, hτ⟩ := exists_successorDensity μ p.domain p.le_ambient p.contains_null p.density s
  let q : PartialDensity μ := {
    domain := twoCellSigma p.domain s
    le_ambient := twoCellSigma_le p.le_ambient hs
    contains_null := fun t ht => le_twoCellSigma p.domain s t (p.contains_null t ht)
    density := τ }
  exact ⟨q, ⟨le_twoCellSigma p.domain s, hτ⟩, measurableSet_twoCellSigma p.domain s⟩

theorem exists_sequence_upper (f : ℕ → PartialDensity μ) (hf : Monotone f) :
    ∃ q : PartialDensity μ, ∀ n, f n ≤ q := by
  let ℱ : Filtration ℕ m₀ :=
    ⟨fun n => (f n).domain, fun _ _ h => (hf h).1, fun n => (f n).le_ambient⟩
  let ρ : ∀ n, @SetDensity X m₀ (ℱ n) μ := fun n => (f n).density
  let q : PartialDensity μ := {
    domain := ⨆ n, ℱ n
    le_ambient := iSup_le ℱ.le
    contains_null := fun s hs => le_iSup (fun n => ℱ n) 0 s ((f 0).contains_null s hs)
    density := countableDensity μ ℱ ρ }
  refine ⟨q, ?_⟩
  intro n
  refine ⟨le_iSup (fun n => ℱ n) n, ?_⟩
  intro s hs
  exact countableDensity_extends μ ℱ ρ (fun i j hij t ht => (hf hij).2 t ht) n hs

end PartialDensity
end Gelfand516Lifting
end
end Gelfand516Source8

/- Source: Work.Gelfand516.Lifting.ChainDichotomy; SHA256 ecbbd4699c1d00e898dedddd9cebe44b705c2b76565b0f18ff72fa212cd17f23. -/
section Gelfand516Source9

set_option autoImplicit false
noncomputable section
open Set

namespace Gelfand516Lifting
universe u
variable {α : Type u} [Preorder α]

/-- A chain either has an increasing countable cofinal sequence, or every
countable family in it has an upper bound still belonging to the chain. -/
theorem chain_countable_dichotomy (C : Set α) (hc : IsChain (· ≤ ·) C) :
    (∃ f : ℕ → α, (∀ n, f n ∈ C) ∧ Monotone f ∧ ∀ a ∈ C, ∃ n, a ≤ f n) ∨
    (∀ f : ℕ → α, (∀ n, f n ∈ C) → ∃ a ∈ C, ∀ n, f n ≤ a) := by
  classical
  by_cases hcof : ∃ f : ℕ → C, ∀ a : C, ∃ n, a ≤ f n
  · obtain ⟨f, hf⟩ := hcof
    have hupper : ∀ a b : C, ∃ c : C, a ≤ c ∧ b ≤ c := by
      intro a b
      obtain ⟨c, hmem, hac, hbc⟩ := hc.directedOn a.val a.property b.val b.property
      exact ⟨⟨c, hmem⟩, hac, hbc⟩
    choose upper hleft hright using hupper
    let g : ℕ → C := Nat.rec (f 0) (fun n prev => upper prev (f (n + 1)))
    have hzero : g 0 = f 0 := rfl
    have hsucc (n : ℕ) : g (n + 1) = upper (g n) (f (n + 1)) := rfl
    have hmono : Monotone g := monotone_nat_of_le_succ (fun n => by
      rw [hsucc]
      exact hleft _ _)
    have hfg (n : ℕ) : f n ≤ g n := by
      cases n with
      | zero => exact le_of_eq hzero.symm
      | succ n => rw [hsucc]; exact hright _ _
    refine Or.inl ⟨fun n => (g n).val, fun n => (g n).property, ?_, ?_⟩
    · intro n m hnm
      exact hmono hnm
    · intro a ha
      obtain ⟨n, hn⟩ := hf ⟨a, ha⟩
      exact ⟨n, hn.trans (hfg n)⟩
  · apply Or.inr
    intro f hf
    let f' : ℕ → C := fun n => ⟨f n, hf n⟩
    have hnot : ¬ ∀ a : C, ∃ n, a ≤ f' n := fun h => hcof ⟨f', h⟩
    push_neg at hnot
    obtain ⟨a, ha⟩ := hnot
    refine ⟨a.val, a.property, ?_⟩
    intro n
    rcases hc.total (hf n) a.property with hle | hle
    · exact hle
    · exact False.elim (ha n hle)

end Gelfand516Lifting
end
end Gelfand516Source9

/- Source: Work.Gelfand516.Lifting.ChainDensity; SHA256 a3e80c2166a02a1ddd32bee50ee41a107d8f2e4893f82a450dc6691f825e8961. -/
section Gelfand516Source10

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory

namespace Gelfand516Lifting
universe u
variable {X : Type u} {m₀ : MeasurableSpace X} (μ : @Measure X m₀)

namespace PartialDensity
variable (C : Set (PartialDensity μ)) (hC : C.Nonempty)
  (hbounded : ∀ f : ℕ → PartialDensity μ, (∀ n, f n ∈ C) → ∃ p ∈ C, ∀ n, f n ≤ p)

/-- When countable subfamilies of a chain have a bound still in the chain,
the literal union of its domain sigma-algebras is a sigma-algebra. -/
def chainSigma : MeasurableSpace X where
  MeasurableSet' s := ∃ p ∈ C, MeasurableSet[p.domain] s
  measurableSet_empty := ⟨hC.some, hC.some_mem, @MeasurableSet.empty X hC.some.domain⟩
  measurableSet_compl := by
    rintro s ⟨p, hp, hs⟩
    exact ⟨p, hp, hs.compl⟩
  measurableSet_iUnion := by
    intro s hs
    choose p hp hsp using hs
    obtain ⟨q, hq, hpq⟩ := hbounded p hp
    exact ⟨q, hq, MeasurableSet.iUnion (fun n => (hpq n).1 (s n) (hsp n))⟩

include hC hbounded in
theorem exists_chain_union_upper (hc : IsChain (· ≤ ·) C) :
    ∃ q : PartialDensity μ, ∀ p ∈ C, p ≤ q := by
  classical
  let M := chainSigma μ C hC hbounded
  let D := {s : Set X // MeasurableSet[M] s}
  have hex (s : D) : ∃ p ∈ C, MeasurableSet[p.domain] s.val := s.property
  choose chosen hchosen hmeas using hex
  let f : Set X → Set X := fun s => if hs : MeasurableSet[M] s then
    (chosen ⟨s, hs⟩).density.toFun s else ∅
  have hf (s : Set X) (hs : MeasurableSet[M] s) (p : PartialDensity μ)
      (hp : p ∈ C) (hsp : MeasurableSet[p.domain] s) : f s = p.density.toFun s := by
    dsimp only [f]
    rw [dif_pos hs]
    rcases hc.total (hchosen ⟨s, hs⟩) hp with hle | hle
    · exact ((hle.2 s (hmeas ⟨s, hs⟩))).symm
    · exact hle.2 s hsp
  have hfmeas (s : Set X) (hs : MeasurableSet[M] s) : MeasurableSet[M] (f s) := by
    rw [hf s hs (chosen ⟨s, hs⟩) (hchosen ⟨s, hs⟩) (hmeas ⟨s, hs⟩)]
    exact ⟨chosen ⟨s, hs⟩, hchosen ⟨s, hs⟩,
      (chosen ⟨s, hs⟩).density.measurable s (hmeas ⟨s, hs⟩)⟩
  have hfrep (s : Set X) (hs : MeasurableSet[M] s) : ∀ᵐ x ∂μ, x ∈ f s ↔ x ∈ s := by
    rw [hf s hs (chosen ⟨s, hs⟩) (hchosen ⟨s, hs⟩) (hmeas ⟨s, hs⟩)]
    exact (chosen ⟨s, hs⟩).density.ae_rep s (hmeas ⟨s, hs⟩)
  have hcommon (s t : Set X) (hs : MeasurableSet[M] s) (ht : MeasurableSet[M] t) :
      ∃ p ∈ C, MeasurableSet[p.domain] s ∧ MeasurableSet[p.domain] t := by
    obtain ⟨p, hp, hsp, htp⟩ := hc.directedOn _ (hchosen ⟨s, hs⟩) _ (hchosen ⟨t, ht⟩)
    exact ⟨p, hp, hsp.1 s (hmeas ⟨s, hs⟩), htp.1 t (hmeas ⟨t, ht⟩)⟩
  have hfcongr (s t : Set X) (hs : MeasurableSet[M] s) (ht : MeasurableSet[M] t)
      (hst : ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t) : f s = f t := by
    obtain ⟨p, hp, hsp, htp⟩ := hcommon s t hs ht
    rw [hf s hs p hp hsp, hf t ht p hp htp]
    exact p.density.congr s t hsp htp hst
  have hfempty : f ∅ = ∅ := by
    rw [hf ∅ (@MeasurableSet.empty X M) hC.some hC.some_mem
      (@MeasurableSet.empty X hC.some.domain)]
    exact hC.some.density.empty
  have hfinter (s t : Set X) (hs : MeasurableSet[M] s) (ht : MeasurableSet[M] t) :
      f (s ∩ t) = f s ∩ f t := by
    obtain ⟨p, hp, hsp, htp⟩ := hcommon s t hs ht
    rw [hf (s ∩ t) (hs.inter ht) p hp (hsp.inter htp), hf s hs p hp hsp, hf t ht p hp htp]
    exact p.density.inter s t hsp htp
  let τ : @SetDensity X m₀ M μ := ⟨f, hfmeas, hfrep, hfcongr, hfempty, hfinter⟩
  let q : PartialDensity μ := {
    domain := M
    le_ambient := fun s hs => by
      obtain ⟨p, hp, hsp⟩ := hs
      exact p.le_ambient s hsp
    contains_null := fun s hs => ⟨hC.some, hC.some_mem, hC.some.contains_null s hs⟩
    density := τ }
  refine ⟨q, ?_⟩
  intro p hp
  exact ⟨fun s hs => ⟨p, hp, hs⟩, fun s hs => hf s ⟨p, hp, hs⟩ p hp hs⟩

end PartialDensity

variable [IsFiniteMeasure μ]

theorem partialDensity_chains_bounded (C : Set (PartialDensity μ))
    (hc : IsChain (· ≤ ·) C) (hC : C.Nonempty) : BddAbove C := by
  rcases chain_countable_dichotomy C hc with ⟨f, hfC, hfmono, hfcof⟩ | hbounded
  · obtain ⟨q, hq⟩ := PartialDensity.exists_sequence_upper μ f hfmono
    refine ⟨q, ?_⟩
    intro p hp
    obtain ⟨n, hn⟩ := hfcof p hp
    exact hn.trans (hq n)
  · obtain ⟨q, hq⟩ := PartialDensity.exists_chain_union_upper μ C hC hbounded hc
    exact ⟨q, hq⟩

/-- Fremlin341H for finite nonzero complete measures, proved by Zorn with the
actual successor and countable-limit extensions. -/
theorem exists_setDensity_of_finite_complete
    (hcomplete : ∀ s : Set X, μ s = 0 → MeasurableSet[m₀] s)
    (hnonnull : μ univ ≠ 0) : Nonempty (@SetDensity X m₀ m₀ μ) := by
  letI : Nonempty (PartialDensity μ) := ⟨PartialDensity.initial μ hcomplete hnonnull⟩
  obtain ⟨p, hp⟩ := zorn_le_nonempty (partialDensity_chains_bounded μ)
  have hle : m₀ ≤ p.domain := by
    intro s hs
    obtain ⟨q, hpq, hqs⟩ := PartialDensity.exists_adjoin μ p s hs
    exact (hp hpq).1 s hqs
  have he : p.domain = m₀ := le_antisymm p.le_ambient hle
  exact ⟨Eq.mp (congrArg (fun m => @SetDensity X m₀ m μ) he) p.density⟩

end Gelfand516Lifting
end
end Gelfand516Source10

/- Source: Work.Gelfand516.Lifting.EnhancedSetDensity; SHA256 54aeb6fee3a75e8c8606f966a618ed812bcd337785df615a3bd4ee8d0567d858. -/
section Gelfand516Source11

set_option autoImplicit false
noncomputable section
open Set GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Lifting
universe u
variable {X : Type u}

/-- A lower density on measurable sets, expressed directly using the exact
canonical enhanced measurable and negligible predicates. -/
structure EnhancedSetDensity (E : Enhanced X) where
  toFun : Set X → Set X
  measurable : ∀ s, s ∈ E.measurable → toFun s ∈ E.measurable
  rep : ∀ s, s ∈ E.measurable → symmDiff (toFun s) s ∈ E.negligible
  congr : ∀ s t, s ∈ E.measurable → t ∈ E.measurable →
    symmDiff s t ∈ E.negligible → toFun s = toFun t
  empty : toFun ∅ = ∅
  inter : ∀ s t, s ∈ E.measurable → t ∈ E.measurable →
    toFun (s ∩ t) = toFun s ∩ toFun t

/-- Null components are retained with their constant-empty lower density;
no componentwise nontriviality assumption is needed for gluing. -/
def EnhancedSetDensity.of_null (E : Enhanced X) (hnull : (univ : Set X) ∈ E.negligible) :
    EnhancedSetDensity E where
  toFun := fun _ => ∅
  measurable := fun _ _ => E.sigmaAlgebra.1
  rep := fun s _ => E.sigmaIdeal.2.1 _ _ (subset_univ _) hnull
  congr := fun _ _ _ _ _ => rfl
  empty := rfl
  inter := fun _ _ _ _ => by simp only [inter_self]

end Gelfand516Lifting
end
end Gelfand516Source11

/- Source: Work.Gelfand516.Lifting.PointwiseExtension; SHA256 3a545c2a2c464fee299c85f41e19d393bd186d4336a6937b13c3d97641feea2a. -/
section Gelfand516Source12

set_option autoImplicit false
noncomputable section
open Set

namespace Gelfand516Lifting
universe u v
variable {B : Type u} [BooleanAlgebra B]

/-- A proper Boolean ideal can be killed by a two-valued homomorphism. -/
theorem exists_booleanHom_killing_ideal (I : Order.Ideal B) (htop : (⊤ : B) ∉ I) :
    ∃ p : BoundedLatticeHom B Bool, ∀ a ∈ I, p a = false := by
  classical
  have hd : Disjoint (Order.PFilter.principal (⊤ : B) : Set B) (I : Set B) := by
    apply Set.disjoint_left.mpr
    intro a ha hIa
    have htopa : (⊤ : B) ≤ a := ha
    have heq : a = ⊤ := le_antisymm le_top htopa
    exact htop (heq ▸ hIa)
  obtain ⟨J, hJ, hIJ, _⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  let p : BoundedLatticeHom B Bool := {
    toFun := fun a => decide (a ∉ J)
    map_sup' := by
      intro a c
      by_cases ha : a ∈ J <;> by_cases hc : c ∈ J <;>
        simp [Order.Ideal.sup_mem_iff, ha, hc]
    map_inf' := by
      intro a c
      have hi : a ⊓ c ∈ J ↔ a ∈ J ∨ c ∈ J :=
        ⟨hJ.mem_or_mem, fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
      by_cases ha : a ∈ J <;> by_cases hc : c ∈ J <;> simp [hi, ha, hc]
    map_top' := by simp [hJ.toIsProper.top_notMem]
    map_bot' := by simp [J.bot_mem] }
  refine ⟨p, ?_⟩
  intro a ha
  have hJa : a ∈ J := hIJ ha
  change decide (a ∉ J) = false
  simp [hJa]

variable {X : Type v} [Nontrivial B]

theorem monotone_of_map_inf (θ : B → Set X)
    (hinf : ∀ a b, θ (a ⊓ b) = θ a ∩ θ b) : Monotone θ := by
  intro a b hab x hx
  have h : x ∈ θ (a ⊓ b) := by simpa only [inf_eq_left.mpr hab] using hx
  rw [hinf] at h
  exact h.2

/-- Pointwise prime-ideal separation extends a bottom- and meet-preserving set
map to a Boolean homomorphism above it. -/
theorem exists_point_extension (θ : B → Set X) (hbot : θ ⊥ = ∅)
    (hinf : ∀ a b, θ (a ⊓ b) = θ a ∩ θ b) (x : X) :
    ∃ p : BoundedLatticeHom B Bool, ∀ a, x ∈ θ a → p a = true := by
  classical
  have hmono := monotone_of_map_inf θ hinf
  by_cases hx : x ∈ θ ⊤
  · let I : Order.Ideal B := {
      carrier := {a | x ∈ θ aᶜ}
      lower' := by
        intro a b hab hb
        exact hmono (compl_le_compl hab) hb
      nonempty' := ⟨⊥, by simpa using hx⟩
      directed' := by
        intro a ha b hb
        refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
        change x ∈ θ (a ⊔ b)ᶜ
        rw [compl_sup, hinf]
        exact ⟨ha, hb⟩ }
    have htop : (⊤ : B) ∉ I := by
      intro h
      change x ∈ θ (⊤ : B)ᶜ at h
      simpa [hbot] using h
    obtain ⟨p, hp⟩ := exists_booleanHom_killing_ideal I htop
    refine ⟨p, ?_⟩
    intro a ha
    have hac : aᶜ ∈ I := by
      change x ∈ θ aᶜᶜ
      simpa only [compl_compl] using ha
    have hcomp : p aᶜ = false := hp _ hac
    rw [map_compl] at hcomp
    cases hpa : p a <;> simp_all
  · have htop : (⊤ : B) ∉ (Order.Ideal.principal (⊥ : B) : Order.Ideal B) := by
      intro h
      have hle : (⊤ : B) ≤ ⊥ := h
      exact top_ne_bot (le_bot_iff.mp hle)
    obtain ⟨p, _⟩ := exists_booleanHom_killing_ideal (Order.Ideal.principal (⊥ : B)) htop
    exact ⟨p, fun a ha => False.elim (hx (hmono le_top ha))⟩

/-- Algebraic completion of a lower density, before proving measurability by
the representative sandwich. This is the prime-ideal step of Fremlin 341J. -/
theorem exists_booleanHom_above (θ : B → Set X) (hbot : θ ⊥ = ∅)
    (hinf : ∀ a b, θ (a ⊓ b) = θ a ∩ θ b) :
    ∃ φ : BoundedLatticeHom B (Set X), ∀ a, θ a ⊆ φ a := by
  classical
  choose p hp using fun x : X => exists_point_extension θ hbot hinf x
  let φ : BoundedLatticeHom B (Set X) := {
    toFun := fun a => {x | p x a = true}
    map_sup' := by
      intro a b
      ext x
      change p x (a ⊔ b) = true ↔ p x a = true ∨ p x b = true
      rw [map_sup]
      cases p x a <;> cases p x b <;> decide
    map_inf' := by
      intro a b
      ext x
      change p x (a ⊓ b) = true ↔ p x a = true ∧ p x b = true
      rw [map_inf]
      cases p x a <;> cases p x b <;> decide
    map_top' := by
      ext x
      change p x ⊤ = true ↔ True
      rw [map_top]
      decide
    map_bot' := by
      ext x
      change p x ⊥ = true ↔ False
      rw [map_bot]
      decide }
  exact ⟨φ, fun a x hx => hp x a hx⟩

end Gelfand516Lifting
end
end Gelfand516Source12

/- Source: Work.Gelfand516.SectionMap; SHA256 604d9672ba52b34efe9845a25bdc9c9e824a7e11dc5cb7d028b34e39be943c20. -/
section Gelfand516Source13

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516
universe u
variable {X B : Type u} [BooleanAlgebra B]

/-- Explicit lifting data for the canonical quotient. Existence of this data
is the von Neumann--Maharam theorem and is not asserted here. -/
structure BooleanSection (E : Enhanced X) (e : MmodN E ≃o B) where
  toHom : BoundedLatticeHom B (Set X)
  measurable : ∀ b, toHom b ∈ E.measurable
  quotient_section : ∀ b, e (MmodN.mk (toHom b) (measurable b)) = b

def basic (b : B) : Set (stoneSpectrum B) :=
  {p | (show BoundedLatticeHom B Bool from p) b = true}

theorem basic_top : basic (⊤ : B) = univ := by
  ext p
  change (show BoundedLatticeHom B Bool from p) ⊤ = true ↔ True
  rw [map_top]
  decide

theorem basic_bot : basic (⊥ : B) = ∅ := by
  ext p
  change (show BoundedLatticeHom B Bool from p) ⊥ = true ↔ False
  rw [map_bot]
  decide

theorem basic_inf (a b : B) : basic (a ⊓ b) = basic a ∩ basic b := by
  ext p
  change (show BoundedLatticeHom B Bool from p) (a ⊓ b) = true ↔
    (show BoundedLatticeHom B Bool from p) a = true ∧
      (show BoundedLatticeHom B Bool from p) b = true
  rw [map_inf]
  cases (show BoundedLatticeHom B Bool from p) a <;>
    cases (show BoundedLatticeHom B Bool from p) b <;> decide

theorem basic_compl (b : B) : basic bᶜ = (basic b)ᶜ := by
  ext p
  change (show BoundedLatticeHom B Bool from p) bᶜ = true ↔
    ¬(show BoundedLatticeHom B Bool from p) b = true
  rw [map_compl]
  cases (show BoundedLatticeHom B Bool from p) b <;> decide

theorem basic_isOpen (b : B) : IsOpen (basic b) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨b, rfl⟩

theorem basic_isClosed (b : B) : IsClosed (basic b) := by
  apply isOpen_compl_iff.mp
  rw [← basic_compl]
  exact basic_isOpen _

theorem basic_measurable (b : B) : basic b ∈ (TM (stoneSpectrum B)).measurable :=
  (baire_iff _).2 (basic_isOpen b).baireMeasurableSet

variable {E : Enhanced X} {e : MmodN E ≃o B} (θ : BooleanSection E e)

/-- Point evaluation of an explicit Boolean section is a point of the exact
frozen Stone spectrum. -/
def sectionPoint (x : X) : stoneSpectrum B := by
  classical
  exact
    { toFun := fun b => decide (x ∈ θ.toHom b)
      map_sup' := fun a b => by simp [map_sup]
      map_inf' := fun a b => by simp [map_inf]
      map_top' := by simp
      map_bot' := by simp }

theorem sectionPoint_preimage_basic (b : B) :
    sectionPoint θ ⁻¹' basic b = θ.toHom b := by
  ext x
  simp [sectionPoint, basic]

theorem sectionPoint_basic_class (b : B) :
    e (MmodN.mk (sectionPoint θ ⁻¹' basic b)
      (by rw [sectionPoint_preimage_basic]; exact θ.measurable b)) = b := by
  simpa only [sectionPoint_preimage_basic] using θ.quotient_section b

theorem section_injective : Function.Injective θ.toHom := by
  intro a b hab
  have hq : MmodN.mk (θ.toHom a) (θ.measurable a) =
      MmodN.mk (θ.toHom b) (θ.measurable b) :=
    congrArg (Quotient.mk (nullSetoid E)) (Subtype.ext hab)
  exact (θ.quotient_section a).symm.trans ((congrArg e hq).trans (θ.quotient_section b))

include θ in
theorem basic_nonempty_of_ne_bot {b : B} (hb : b ≠ ⊥) : (basic b).Nonempty := by
  have hn : (θ.toHom b).Nonempty := by
    by_contra h
    have he : θ.toHom b = θ.toHom ⊥ :=
      (not_nonempty_iff_eq_empty.mp h).trans (map_bot θ.toHom).symm
    exact hb (section_injective θ he)
  obtain ⟨x, hx⟩ := hn
  exact ⟨sectionPoint θ x, by
    change x ∈ sectionPoint θ ⁻¹' basic b
    rwa [sectionPoint_preimage_basic]⟩

theorem sectionPoint_preimage_rep (s : Set X) (hs : s ∈ E.measurable) :
    symmDiff s (sectionPoint θ ⁻¹' basic (e (MmodN.mk s hs))) ∈ E.negligible := by
  rw [sectionPoint_preimage_basic]
  have he : MmodN.mk s hs =
      MmodN.mk (θ.toHom (e (MmodN.mk s hs))) (θ.measurable _) := by
    apply e.injective
    exact (θ.quotient_section _).symm
  exact Quotient.exact he

end Gelfand516
end
end Gelfand516Source13

/- Source: Work.Gelfand516.StoneTopology; SHA256 68008c39dde24d52b0919abff31e048234d4394ea270f163ae112018eb8ff724. -/
section Gelfand516Source14

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516
universe u

section Boolean
variable {X B : Type u} [BooleanAlgebra B]
variable {E : Enhanced X} {e : MmodN E ≃o B} (θ : BooleanSection E e)

theorem basic_mono : Monotone (basic (B := B)) := by
  intro a b hab p hp
  change (show BoundedLatticeHom B Bool from p) a = true at hp
  change (show BoundedLatticeHom B Bool from p) b = true
  have h := OrderHomClass.mono (show BoundedLatticeHom B Bool from p) hab
  rw [hp] at h
  exact top_le_iff.mp h

include θ in
theorem basic_le_iff {a b : B} : basic a ⊆ basic b ↔ a ≤ b := by
  constructor
  · intro h
    have hh : θ.toHom a ⊆ θ.toHom b := by
      rw [← sectionPoint_preimage_basic θ a, ← sectionPoint_preimage_basic θ b]
      exact preimage_mono h
    apply inf_eq_left.mp
    apply section_injective θ
    rw [map_inf]
    exact inter_eq_left.mpr hh
  · intro h
    exact basic_mono h

theorem basic_basis : IsTopologicalBasis {U : Set (stoneSpectrum B) | ∃ b : B, U = basic b} := by
  have hb := isTopologicalBasis_of_subbasis_of_inter
    (r := {U : Set (stoneSpectrum B) | ∃ b : B, U = basic b}) rfl
    (by
      rintro s ⟨a, rfl⟩ t ⟨b, rfl⟩
      exact ⟨a ⊓ b, (basic_inf a b).symm⟩)
  have hu : (univ : Set (stoneSpectrum B)) ∈ {U | ∃ b : B, U = basic b} :=
    ⟨⊤, basic_top.symm⟩
  simpa only [insert_eq_of_mem hu] using hb

theorem exists_basic_of_mem_open {U : Set (stoneSpectrum B)} {p : stoneSpectrum B}
    (hp : p ∈ U) (hU : IsOpen U) : ∃ b : B, p ∈ basic b ∧ basic b ⊆ U := by
  obtain ⟨V, ⟨b, rfl⟩, hp, hV⟩ := basic_basis.exists_subset_of_mem_open hp hU
  exact ⟨b, hp, hV⟩

end Boolean

section Complete
variable {X B : Type u} [CompleteBooleanAlgebra B]
variable {E : Enhanced X} {e : MmodN E ≃o B} (θ : BooleanSection E e)

include θ in
/-- Completeness of the Boolean algebra makes closures of opens basic clopens.
The explicit section supplies the point separation used in this proof. -/
theorem closure_eq_basic {U : Set (stoneSpectrum B)} (hU : IsOpen U) :
    closure U = basic (sSup {b : B | basic b ⊆ U}) := by
  let D : Set B := {b | basic b ⊆ U}
  let b : B := sSup D
  have hUb : U ⊆ basic b := by
    intro p hp
    obtain ⟨c, hpc, hc⟩ := exists_basic_of_mem_open hp hU
    exact basic_mono (le_sSup hc) hpc
  apply subset_antisymm (closure_minimal hUb (basic_isClosed b))
  intro p hp
  by_contra hpU
  obtain ⟨c, hpc, hc⟩ := exists_basic_of_mem_open
    (show p ∈ basic b ∩ (closure U)ᶜ from ⟨hp, hpU⟩)
    ((basic_isOpen b).inter isClosed_closure.isOpen_compl)
  have hcb : c ≤ b := (basic_le_iff θ).1 (fun _ hx => (hc hx).1)
  have hdis : Disjoint c b := by
    apply disjoint_sSup_iff.mpr
    intro a ha
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    apply (basic_le_iff θ).mp
    intro q hq
    rw [basic_inf] at hq
    exact False.elim ((hc hq.1).2 (subset_closure (ha hq.2)))
  have hzero : c = ⊥ := hdis.eq_bot_of_le hcb
  simpa only [hzero, basic_bot, mem_empty_iff_false] using hpc

include θ in
/-- Every canonical Baire-measurable set has a basic clopen representative
modulo a meagre set; no claim that a section exists is used here. -/
theorem baire_basic_rep {s : Set (stoneSpectrum B)} (hs : s ∈ (TM (stoneSpectrum B)).measurable) :
    ∃ b : B, IsMeagre (symmDiff s (basic b)) := by
  obtain ⟨U, hU, hsU⟩ := hs
  refine ⟨sSup {b : B | basic b ⊆ U}, ?_⟩
  rw [← closure_eq_basic θ hU]
  apply (isMeagre_symmDiff_iff _ _).mpr
  exact ((isMeagre_symmDiff_iff _ _).mp hsU).trans (closure_residualEq hU.isLocallyClosed).symm

end Complete
end Gelfand516
end
end Gelfand516Source14

/- Source: Work.Gelfand516.CompactInverseTopology; SHA256 7db21be779142bc0479790653802ed57108a0624e0cfbe0e947b556057d28144. -/
section Gelfand516Source15

set_option autoImplicit false
noncomputable section
open Set GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Compact
open Gelfand516
universe u
variable {B : Type u} [BooleanAlgebra B]

/-- Stone point separation follows from the Boolean prime ideal theorem,
independently of any measurable lifting. -/
theorem basic_nonempty {b : B} (hb : b ≠ ⊥) : (basic b).Nonempty := by
  classical
  have hd : Disjoint (Order.PFilter.principal b : Set B)
      (Order.Ideal.principal (⊥ : B) : Set B) := by
    apply Set.disjoint_left.mpr
    intro x hx hxb
    have hbx : b ≤ x := hx
    have hxb' : x ≤ ⊥ := hxb
    exact hb (le_bot_iff.mp (hbx.trans hxb'))
  obtain ⟨J, hJ, _, hdis⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hd
  have hbJ : b ∉ J := fun h => Set.disjoint_left.mp hdis (le_refl b) h
  let p : BoundedLatticeHom B Bool := {
    toFun := fun a => decide (a ∉ J)
    map_sup' := by
      intro a c
      by_cases ha : a ∈ J <;> by_cases hc : c ∈ J <;>
        simp [Order.Ideal.sup_mem_iff, ha, hc]
    map_inf' := by
      intro a c
      have hi : a ⊓ c ∈ J ↔ a ∈ J ∨ c ∈ J :=
        ⟨hJ.mem_or_mem, fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
      by_cases ha : a ∈ J <;> by_cases hc : c ∈ J <;> simp [hi, ha, hc]
    map_top' := by simp [hJ.toIsProper.top_notMem]
    map_bot' := by simp [J.bot_mem] }
  refine ⟨p, ?_⟩
  change decide (b ∉ J) = true
  simpa only [decide_eq_true_eq] using hbJ

theorem basic_subset_iff {a b : B} : basic a ⊆ basic b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    have hne : a ⊓ bᶜ ≠ ⊥ := by
      rw [← _root_.sdiff_eq]
      exact fun hz => hn (_root_.sdiff_eq_bot_iff.mp hz)
    obtain ⟨p, hp⟩ := basic_nonempty hne
    rw [basic_inf, basic_compl] at hp
    exact hp.2 (h hp.1)
  · intro h
    exact basic_mono h

end Gelfand516Compact
end
end Gelfand516Source15

/- Source: Work.Gelfand516.EnvelopePremap; SHA256 9add3c4e2a7a2b0155b674ac9b3b9aa71210328eb0019cd16b680e18d706a71b. -/
section Gelfand516Source16

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516
universe u
variable {X B : Type u}

/-- Measurable envelopes for arbitrary subsets. A measurable part of the
envelope disjoint from the original set is negligible. This hypothesis is
explicit: its derivation from strict localizability is a separate obligation. -/
def HasMeasurableHulls (E : Enhanced X) : Prop :=
  ∀ s : Set X, ∃ H : Set X, H ∈ E.measurable ∧ s ⊆ H ∧
    ∀ m : Set X, m ∈ E.measurable → m ⊆ H → Disjoint m s → m ∈ E.negligible

@[instance_reducible] def enhancedMeasurableSpace (E : Enhanced X) : MeasurableSpace X where
  MeasurableSet' s := s ∈ E.measurable
  measurableSet_empty := E.sigmaAlgebra.1
  measurableSet_compl := E.sigmaAlgebra.2.1
  measurableSet_iUnion := E.sigmaAlgebra.2.2

variable [CompleteBooleanAlgebra B]
variable {E : Enhanced X} {e : MmodN E ≃o B} (θ : BooleanSection E e)

include θ in
theorem class_eq_bot_iff (s : Set X) (hs : s ∈ E.measurable) :
    e (MmodN.mk s hs) = ⊥ ↔ s ∈ E.negligible := by
  have he : e (MmodN.mk ∅ E.sigmaAlgebra.1) = ⊥ := by
    have hq : MmodN.mk (θ.toHom ⊥) (θ.measurable ⊥) =
        MmodN.mk ∅ E.sigmaAlgebra.1 :=
      congrArg (Quotient.mk (nullSetoid E)) (Subtype.ext (map_bot θ.toHom))
    exact (congrArg e hq).symm.trans (θ.quotient_section ⊥)
  rw [← he, e.injective.eq_iff]
  constructor
  · intro h
    have h' := Quotient.exact h
    change (s \ ∅) ∪ (∅ \ s) ∈ E.negligible at h'
    simpa only [sdiff_empty, empty_sdiff, union_empty] using h'
  · intro h
    apply Quotient.sound
    change (s \ ∅) ∪ (∅ \ s) ∈ E.negligible
    simpa only [sdiff_empty, empty_sdiff, union_empty] using h

/-- The measurable-envelope argument of Fremlin341P(b): nowhere dense sets
pull back to negligible sets under the point map of a Boolean section. -/
theorem sectionPoint_preimage_nowhereDense (hE : HasMeasurableHulls E)
    {F : Set (stoneSpectrum B)} (hF : IsNowhereDense F) :
    sectionPoint θ ⁻¹' F ∈ E.negligible := by
  classical
  letI := enhancedMeasurableSpace E
  obtain ⟨H, hHm, hsub, hH⟩ := hE (sectionPoint θ ⁻¹' F)
  apply negligible_mono E hsub
  by_contra hHN
  let b := e (MmodN.mk H hHm)
  have hb : b ≠ ⊥ := fun h => hHN ((class_eq_bot_iff θ H hHm).1 h)
  have hd : Dense (closure F)ᶜ :=
    (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure, hF.closure⟩).2
  obtain ⟨p, hpF, hpb⟩ := hd.exists_mem_open (basic_isOpen b)
    (basic_nonempty_of_ne_bot θ hb)
  obtain ⟨c, hpc, hc⟩ := exists_basic_of_mem_open
    (show p ∈ basic b ∩ (closure F)ᶜ from ⟨hpb, hpF⟩)
    ((basic_isOpen b).inter isClosed_closure.isOpen_compl)
  have hcb : c ≤ b := (basic_le_iff θ).mp (fun _ hx => (hc hx).1)
  have hcH : θ.toHom c \ H ∈ E.negligible := by
    change MmodN.mk (θ.toHom c) (θ.measurable c) ≤ MmodN.mk H hHm
    apply e.le_iff_le.mp
    rwa [θ.quotient_section]
  have hcm : θ.toHom c ∩ H ∈ E.measurable :=
    (show MeasurableSet (θ.toHom c) from θ.measurable c).inter
      (show MeasurableSet H from hHm)
  have hci : θ.toHom c ∩ H ∈ E.negligible := by
    apply hH _ hcm inter_subset_right
    apply Set.disjoint_left.mpr
    intro x hx hxF
    have hxc : sectionPoint θ x ∈ basic c := by
      change x ∈ sectionPoint θ ⁻¹' basic c
      rw [sectionPoint_preimage_basic]
      exact hx.1
    exact (hc hxc).2 (subset_closure hxF)
  have hcN : θ.toHom c ∈ E.negligible := by
    have heq : θ.toHom c = (θ.toHom c \ H) ∪ (θ.toHom c ∩ H) := by
      ext x
      simp only [mem_union, mem_sdiff, mem_inter_iff]
      tauto
    rw [heq]
    exact negligible_union E hcH hci
  have hzero : c = ⊥ := by
    rw [← θ.quotient_section c]
    exact (class_eq_bot_iff θ _ (θ.measurable c)).2 hcN
  simpa only [hzero, basic_bot, mem_empty_iff_false] using hpc

theorem sectionPoint_preimage_meagre (hE : HasMeasurableHulls E)
    {F : Set (stoneSpectrum B)} (hF : IsMeagre F) :
    sectionPoint θ ⁻¹' F ∈ E.negligible := by
  classical
  obtain ⟨S, hS, hcount, hsub⟩ := isMeagre_iff_countable_union_isNowhereDense.mp hF
  rcases S.eq_empty_or_nonempty with rfl | hn
  · apply negligible_mono E (preimage_mono hsub)
    simpa only [sUnion_empty, preimage_empty] using E.sigmaIdeal.1
  · obtain ⟨f, hf⟩ := hcount.exists_eq_range hn
    have hall : ∀ n, sectionPoint θ ⁻¹' f n ∈ E.negligible := by
      intro n
      apply sectionPoint_preimage_nowhereDense θ hE
      apply hS
      rw [hf]
      exact mem_range_self n
    apply negligible_mono E (preimage_mono hsub)
    rw [hf, sUnion_range, preimage_iUnion]
    exact E.sigmaIdeal.2.2 _ hall

theorem sectionPoint_preimage_measurable (hE : HasMeasurableHulls E)
    {s : Set (stoneSpectrum B)} (hs : s ∈ (TM (stoneSpectrum B)).measurable) :
    sectionPoint θ ⁻¹' s ∈ E.measurable := by
  letI := enhancedMeasurableSpace E
  obtain ⟨b, hb⟩ := baire_basic_rep θ hs
  have hn := sectionPoint_preimage_meagre θ hE hb
  have hnM : MeasurableSet (sectionPoint θ ⁻¹' symmDiff s (basic b)) :=
    E.negligibleMeasurable hn
  have hbM : MeasurableSet (sectionPoint θ ⁻¹' basic b) := by
    rw [sectionPoint_preimage_basic]
    exact θ.measurable b
  have heq : sectionPoint θ ⁻¹' s =
      symmDiff (sectionPoint θ ⁻¹' symmDiff s (basic b)) (sectionPoint θ ⁻¹' basic b) := by
    rw [preimage_symmDiff, symmDiff_symmDiff_cancel_right]
  rw [heq]
  exact hnM.symmDiff hbM

/-- A genuine premap into the exact canonical Stone spectrum, conditional on
both a Boolean section and measurable envelopes. Neither assumption is hidden. -/
def sectionPremap (hE : HasMeasurableHulls E) : Premap E (TM (stoneSpectrum B)) :=
  ⟨fun x => some (sectionPoint θ x), by
    have hp (s : Set (stoneSpectrum B)) :
        partialPreimage (fun x => some (sectionPoint θ x)) s = sectionPoint θ ⁻¹' s := by
      ext x
      simp [partialPreimage]
    refine ⟨?_, fun s hs => ?_, fun s hs => ?_⟩
    · have he : (partialDomain (fun x => some (sectionPoint θ x)))ᶜ = ∅ := by
        ext x
        simp [partialDomain]
      rw [he]
      exact E.sigmaIdeal.1
    · rw [hp]
      exact sectionPoint_preimage_measurable θ hE hs
    · rw [hp]
      exact sectionPoint_preimage_meagre θ hE hs⟩

theorem sectionPremap_basic (hE : HasMeasurableHulls E) (b : B) :
    partialPreimage (sectionPremap θ hE).val (basic b) = θ.toHom b := by
  change partialPreimage (fun x => some (sectionPoint θ x)) (basic b) = θ.toHom b
  have he : partialPreimage (fun x => some (sectionPoint θ x)) (basic b) =
      sectionPoint θ ⁻¹' basic b := by ext x; simp [partialPreimage]
  exact he.trans (sectionPoint_preimage_basic θ b)

end Gelfand516
end
end Gelfand516Source16

/- Source: Work.Gelfand516.CompactInverseQuotient; SHA256 c4207d21a04beb51c4de3fc6dabfd37c600cc1c338afef7e592faccd0f432d91. -/
section Gelfand516Source17

set_option autoImplicit false
noncomputable section
open Set GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Compact
universe u
variable {X B : Type u} [BooleanAlgebra B]
variable (E : Enhanced X) (e : MmodN E ≃o B)

theorem class_mono {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (h : a ⊆ b) : e (MmodN.mk a ha) ≤ e (MmodN.mk b hb) := by
  apply e.monotone
  change a \ b ∈ E.negligible
  rw [sdiff_eq_empty.mpr h]
  exact E.sigmaIdeal.1

theorem class_empty : e (MmodN.mk ∅ E.sigmaAlgebra.1) = ⊥ := by
  apply le_antisymm _ bot_le
  have h (q : MmodN E) : e (MmodN.mk ∅ E.sigmaAlgebra.1) ≤ e q := by
    induction q using Quotient.ind with
    | _ q => exact class_mono E e E.sigmaAlgebra.1 q.2 (empty_subset _)
  exact (h (e.symm ⊥)).trans_eq (e.apply_symm_apply _)

theorem class_null_iff (s : Set X) (hs : s ∈ E.measurable) :
    e (MmodN.mk s hs) = ⊥ ↔ s ∈ E.negligible := by
  rw [← class_empty E e, e.injective.eq_iff]
  constructor
  · intro h
    have h' := Quotient.exact h
    change (s \ ∅) ∪ (∅ \ s) ∈ E.negligible at h'
    simpa only [sdiff_empty, empty_sdiff, union_empty] using h'
  · intro h
    apply Quotient.sound
    change (s \ ∅) ∪ (∅ \ s) ∈ E.negligible
    simpa only [sdiff_empty, empty_sdiff, union_empty] using h

theorem class_univ (h : (univ : Set X) ∈ E.measurable) : e (MmodN.mk univ h) = ⊤ := by
  apply le_antisymm le_top
  have hu (q : MmodN E) : e q ≤ e (MmodN.mk univ h) := by
    induction q using Quotient.ind with
    | _ q => exact class_mono E e q.2 h (subset_univ _)
  exact (e.apply_symm_apply ⊤).symm.trans_le (hu (e.symm ⊤))

theorem class_inter (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (hi : a ∩ b ∈ E.measurable) :
    e (MmodN.mk (a ∩ b) hi) = e (MmodN.mk a ha) ⊓ e (MmodN.mk b hb) := by
  have hglb : IsGLB {MmodN.mk a ha, MmodN.mk b hb} (MmodN.mk (a ∩ b) hi) := by
    constructor
    · intro q hq
      rcases hq with rfl | hq
      · exact e.le_iff_le.mp (class_mono E e hi ha inter_subset_left)
      · rcases hq with rfl
        exact e.le_iff_le.mp (class_mono E e hi hb inter_subset_right)
    · intro q hq
      have hqa := hq (mem_insert _ _)
      have hqb := hq (mem_insert_of_mem _ (mem_singleton _))
      induction q using Quotient.ind with
      | _ q =>
        change q.1 \ (a ∩ b) ∈ E.negligible
        rw [sdiff_inter]
        exact negligible_union E hqa hqb
  have h := e.isGLB_image'.2 hglb
  have h' : IsGLB {e (MmodN.mk a ha), e (MmodN.mk b hb)}
      (e (MmodN.mk (a ∩ b) hi)) := by simpa only [image_pair] using h
  exact h'.unique isGLB_pair

theorem class_union (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (hu : a ∪ b ∈ E.measurable) :
    e (MmodN.mk (a ∪ b) hu) = e (MmodN.mk a ha) ⊔ e (MmodN.mk b hb) := by
  have hlub : IsLUB {MmodN.mk a ha, MmodN.mk b hb} (MmodN.mk (a ∪ b) hu) := by
    constructor
    · intro q hq
      rcases hq with rfl | hq
      · exact e.le_iff_le.mp (class_mono E e ha hu subset_union_left)
      · rcases hq with rfl
        exact e.le_iff_le.mp (class_mono E e hb hu subset_union_right)
    · intro q hq
      have hqa := hq (mem_insert _ _)
      have hqb := hq (mem_insert_of_mem _ (mem_singleton _))
      induction q using Quotient.ind with
      | _ q =>
        change (a ∪ b) \ q.1 ∈ E.negligible
        rw [union_sdiff_distrib]
        exact negligible_union E hqa hqb
  have h := e.isLUB_image'.2 hlub
  have h' : IsLUB {e (MmodN.mk a ha), e (MmodN.mk b hb)}
      (e (MmodN.mk (a ∪ b) hu)) := by simpa only [image_pair] using h
  exact h'.unique isLUB_pair

theorem class_compl (s : Set X) (hs : s ∈ E.measurable) :
    e (MmodN.mk sᶜ (E.sigmaAlgebra.2.1 s hs)) = (e (MmodN.mk s hs))ᶜ := by
  letI := Gelfand516.enhancedMeasurableSpace E
  have hsm : MeasurableSet s := hs
  have hum : (univ : Set X) ∈ E.measurable := by
    simpa only [compl_empty] using E.sigmaAlgebra.2.1 ∅ E.sigmaAlgebra.1
  have hi := class_inter E e s sᶜ hs (E.sigmaAlgebra.2.1 s hs) (hsm.inter hsm.compl)
  have hu := class_union E e s sᶜ hs (E.sigmaAlgebra.2.1 s hs) (hsm.union hsm.compl)
  have hi' : e (MmodN.mk s hs) ⊓ e (MmodN.mk sᶜ (E.sigmaAlgebra.2.1 s hs)) = ⊥ := by
    rw [← hi]
    simpa only [inter_compl_self] using class_empty E e
  have hu' : e (MmodN.mk s hs) ⊔ e (MmodN.mk sᶜ (E.sigmaAlgebra.2.1 s hs)) = ⊤ := by
    rw [← hu]
    simpa only [union_compl_self] using class_univ E e hum
  exact (IsCompl.of_eq hi' hu').compl_eq.symm

end Gelfand516Compact
end
end Gelfand516Source17

/- Source: Work.Gelfand516.Lifting.MeasurableExtension; SHA256 43acbab3d918620c3862c6d6e58600975cfa499db4b2f3ddf114f691cb174a1c. -/
section Gelfand516Source18

set_option autoImplicit false
noncomputable section
open Set GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Lifting
universe u
variable {X B : Type u} [BooleanAlgebra B]

/-- A meet-preserving measurable representative of every quotient class. A lower
density need not preserve complements or the top element literally. -/
structure LowerDensity (E : Enhanced X) (e : MmodN E ≃o B) where
  toFun : B → Set X
  map_bot : toFun ⊥ = ∅
  map_inf : ∀ a b, toFun (a ⊓ b) = toFun a ∩ toFun b
  measurable : ∀ b, toFun b ∈ E.measurable
  quotient_section : ∀ b, e (MmodN.mk (toFun b) (measurable b)) = b

variable [Nontrivial B]

/-- Completing a lower density algebraically preserves its quotient classes:
completeness of the enhanced space makes the sandwich representatives measurable.
This is the complete-space step of Fremlin 341I--341J. -/
theorem exists_booleanSection_of_lowerDensity (E : Enhanced X) (e : MmodN E ≃o B)
    (d : LowerDensity E e) : Nonempty (Gelfand516.BooleanSection E e) := by
  classical
  letI := Gelfand516.enhancedMeasurableSpace E
  obtain ⟨φ, habove⟩ := exists_booleanHom_above d.toFun d.map_bot d.map_inf
  have hupper (b : B) : φ b ⊆ (d.toFun bᶜ)ᶜ := by
    intro x hx hxcompl
    have h := habove bᶜ hxcompl
    rw [map_compl] at h
    exact h hx
  have hnull (b : B) : symmDiff (φ b) (d.toFun b) ∈ E.negligible := by
    have hq : MmodN.mk (d.toFun b) (d.measurable b) =
        MmodN.mk (d.toFun bᶜ)ᶜ (E.sigmaAlgebra.2.1 _ (d.measurable bᶜ)) := by
      apply e.injective
      rw [d.quotient_section b,
        Gelfand516Compact.class_compl E e (d.toFun bᶜ) (d.measurable bᶜ),
        d.quotient_section, compl_compl]
    have hn : symmDiff (d.toFun b) (d.toFun bᶜ)ᶜ ∈ E.negligible := Quotient.exact hq
    apply E.sigmaIdeal.2.1 _ _ ?_ hn
    intro x hx
    simp only [mem_symmDiff] at hx ⊢
    rcases hx with h | h
    · exact Or.inr ⟨hupper b h.1, h.2⟩
    · exact False.elim (h.2 (habove b h.1))
  have hmeas (b : B) : φ b ∈ E.measurable := by
    have h₁ : MeasurableSet (d.toFun b) := d.measurable b
    have h₂ : MeasurableSet (symmDiff (φ b) (d.toFun b)) :=
      E.negligibleMeasurable (hnull b)
    have heq : symmDiff (d.toFun b) (symmDiff (φ b) (d.toFun b)) = φ b := by
      ext x
      simp only [mem_symmDiff]
      tauto
    rw [← heq]
    exact h₁.symmDiff h₂
  refine ⟨{ toHom := φ, measurable := hmeas, quotient_section := ?_ }⟩
  intro b
  have hq : MmodN.mk (φ b) (hmeas b) = MmodN.mk (d.toFun b) (d.measurable b) :=
    Quotient.sound (hnull b)
  exact (congrArg e hq).trans (d.quotient_section b)

end Gelfand516Lifting
end
end Gelfand516Source18

/- Source: Work.Gelfand454.FiniteMeasure; SHA256 1807ec0a82e01bce29cbea9b29a0ef9dd52a80923cf65551966fc4b5182ac071. -/
section Gelfand516Source19

open MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand454
universe u

/-- The measurable-space structure already specified by an enhanced space. -/
@[instance_reducible] def measurableSpace {X : Type u} (E : Enhanced X) : MeasurableSpace X where
  MeasurableSet' s := s ∈ E.measurable
  measurableSet_empty := E.sigmaAlgebra.1
  measurableSet_compl := E.sigmaAlgebra.2.1
  measurableSet_iUnion := E.sigmaAlgebra.2.2

section
variable {X : Type u} (E : Enhanced X)

/-- A finite enhanced complex measure is an ordinary complex vector measure.
Its unconstrained values on nonmeasurable sets are replaced by zero. -/
noncomputable def complexMeasureOf (μ : Set X → ℂ)
    (hμ : IsEMeasure E E.measurable μ) : @ComplexMeasure X (measurableSpace E) := by
  classical
  letI : MeasurableSpace X := measurableSpace E
  exact {
    measureOf' s := if s ∈ E.measurable then μ s else 0
    empty' := by
      simp only [E.sigmaAlgebra.1, if_pos]
      exact hμ.2.2.2.2.1 _ E.sigmaIdeal.1
    not_measurable' s hs := if_neg hs
    m_iUnion' f hs hd := by
      have hs' : ∀ i, f i ∈ E.measurable := hs
      have hu := E.sigmaAlgebra.2.2 _ hs'
      simpa only [hs', hu, if_pos] using (hμ.2.2.2.2.2.1 _ hs hd hu).2
  }
theorem complexMeasureOf_apply (μ : Set X → ℂ) (hμ : IsEMeasure E E.measurable μ)
    {s : Set X} (hs : s ∈ E.measurable) : complexMeasureOf E μ hμ s = μ s := by
  exact if_pos hs

/-- A positive finite measure with the same null ideal as a faithful finite
enhanced complex measure. Taking both real variations avoids cancellation. -/
noncomputable def finiteMeasure (μ : Set X → ℂ) (hμ : IsEMeasure E E.measurable μ) :
    @Measure X (measurableSpace E) := by
  letI : MeasurableSpace X := measurableSpace E
  exact
    (ComplexMeasure.re (complexMeasureOf E μ hμ)).totalVariation +
    (ComplexMeasure.im (complexMeasureOf E μ hμ)).totalVariation

instance finiteMeasure_isFinite (μ : Set X → ℂ) (hμ : IsEMeasure E E.measurable μ) :
    IsFiniteMeasure (finiteMeasure E μ hμ) := by
  letI : MeasurableSpace X := measurableSpace E
  unfold finiteMeasure
  infer_instance

theorem finiteMeasure_null_iff_measurable (μ : Set X → ℂ)
    (hμ : IsEMeasure E E.measurable μ) (hf : IsFaithfulEMeasure E E.measurable μ)
    {s : Set X} (hs : s ∈ E.measurable) :
    finiteMeasure E μ hμ s = 0 ↔ s ∈ E.negligible := by
  letI : MeasurableSpace X := measurableSpace E
  have hsm : MeasurableSet s := hs
  rw [finiteMeasure, Measure.add_apply, add_eq_zero,
    SignedMeasure.totalVariation_eq_variation,
    SignedMeasure.totalVariation_eq_variation,
    VectorMeasure.variation_apply_eq_zero hsm,
    VectorMeasure.variation_apply_eq_zero hsm]
  constructor
  · rintro ⟨hr, hi⟩
    apply hf s hs
    intro t ht hts
    apply Complex.ext
    · have h := hr t hts ht
      change (complexMeasureOf E μ hμ t).re = 0 at h
      simpa only [complexMeasureOf_apply E μ hμ ht, Complex.zero_re] using h
    · have h := hi t hts ht
      change (complexMeasureOf E μ hμ t).im = 0 at h
      simpa only [complexMeasureOf_apply E μ hμ ht, Complex.zero_im] using h
  · intro hn
    have hzero : ∀ t, t ⊆ s → t ∈ E.measurable → complexMeasureOf E μ hμ t = 0 := by
      intro t hts ht
      rw [complexMeasureOf_apply E μ hμ ht]
      exact hμ.2.2.2.2.1 _ (negligible_mono E hts hn)
    constructor
    · intro t hts ht
      change (complexMeasureOf E μ hμ t).re = 0
      rw [hzero t hts ht, Complex.zero_re]
    · intro t hts ht
      change (complexMeasureOf E μ hμ t).im = 0
      rw [hzero t hts ht, Complex.zero_im]

theorem finiteMeasure_null_iff (μ : Set X → ℂ)
    (hμ : IsEMeasure E E.measurable μ) (hf : IsFaithfulEMeasure E E.measurable μ)
    (s : Set X) : finiteMeasure E μ hμ s = 0 ↔ s ∈ E.negligible := by
  letI : MeasurableSpace X := measurableSpace E
  constructor
  · intro h
    apply negligible_mono E (subset_toMeasurable (finiteMeasure E μ hμ) s)
    apply (finiteMeasure_null_iff_measurable E μ hμ hf
      (measurableSet_toMeasurable (finiteMeasure E μ hμ) s)).1
    rwa [measure_toMeasurable]
  · intro h
    exact (finiteMeasure_null_iff_measurable E μ hμ hf (E.negligibleMeasurable h)).2 h

/-- The exact canonical sigma-finiteness predicate supplies a finite positive
measure, without adding positivity to its complex-measure hypothesis. -/
theorem exists_finiteMeasure (hE : IsSigmaFiniteE E) :
    ∃ ν : @Measure X (measurableSpace E), IsFiniteMeasure ν ∧ ∀ s : Set X, ν s = 0 ↔ s ∈ E.negligible := by
  letI : MeasurableSpace X := measurableSpace E
  obtain ⟨μ, hμ, hf⟩ := hE
  exact ⟨finiteMeasure E μ hμ, inferInstance, finiteMeasure_null_iff E μ hμ hf⟩

end
end Gelfand454
end Gelfand516Source19

/- Source: Work.Gelfand516.Lifting.EnhancedBridge; SHA256 992ba6a5223a2ca2945a9587ecc8a94ec2ccf3dfb3c3ab42656ee059a452498e. -/
section Gelfand516Source20

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Lifting
universe u
variable {X B : Type u}

/-- An ordinary full-domain density gives the exact enhanced-space data when
its ordinary null sets are precisely the specified negligible sets. -/
def enhancedDensityOfSetDensity (E : Enhanced X)
    (μ : @Measure X (Gelfand454.measurableSpace E))
    (hnull : ∀ s : Set X, μ s = 0 ↔ s ∈ E.negligible)
    (ρ : @SetDensity X (Gelfand454.measurableSpace E) (Gelfand454.measurableSpace E) μ) :
    EnhancedSetDensity E := by
  letI := Gelfand454.measurableSpace E
  refine {
    toFun := ρ.toFun
    measurable := ρ.measurable
    rep := ?_
    congr := ?_
    empty := ρ.empty
    inter := ρ.inter }
  · intro s hs
    apply (hnull _).mp
    apply measure_symmDiff_eq_zero_iff.mpr
    exact (ρ.ae_rep s hs).mono (fun _ h => propext h)
  · intro s t hs ht hst
    apply ρ.congr s t hs ht
    have h := measure_symmDiff_eq_zero_iff.mp ((hnull _).mpr hst)
    filter_upwards [h] with x hx
    change s x ↔ t x
    exact ⟨Eq.mp hx, Eq.mp hx.symm⟩

namespace EnhancedSetDensity
variable (E : Enhanced X) (d : EnhancedSetDensity E)

/-- AE congruence makes the enhanced density descend literally through the
canonical measurable-set quotient. -/
def quotientMap : MmodN E → Set X :=
  Quotient.lift (fun s : {s : Set X // s ∈ E.measurable} => d.toFun s.val)
    (fun s t h => d.congr s.val t.val s.property t.property h)

@[simp] theorem quotientMap_mk (s : Set X) (hs : s ∈ E.measurable) :
    quotientMap E d (MmodN.mk s hs) = d.toFun s := rfl

theorem quotientMap_measurable (q : MmodN E) : quotientMap E d q ∈ E.measurable := by
  induction q using Quotient.ind with
  | _ s => exact d.measurable s.val s.property

theorem quotientMap_class (q : MmodN E) :
    MmodN.mk (quotientMap E d q) (quotientMap_measurable E d q) = q := by
  induction q using Quotient.ind with
  | _ s => exact Quotient.sound (d.rep s.val s.property)

variable [BooleanAlgebra B]

/-- A measure-free enhanced density supplies a lower density on any exact
Boolean presentation of the canonical quotient. -/
def toLowerDensity (e : MmodN E ≃o B) : LowerDensity E e where
  toFun b := quotientMap E d (e.symm b)
  measurable b := quotientMap_measurable E d (e.symm b)
  quotient_section b := by rw [quotientMap_class, e.apply_symm_apply]
  map_bot := by
    have he : e.symm (⊥ : B) = MmodN.mk ∅ E.sigmaAlgebra.1 := by
      apply e.injective
      rw [e.apply_symm_apply, Gelfand516Compact.class_empty E e]
    rw [he, quotientMap_mk, d.empty]
  map_inf := by
    intro a b
    have h (q r : MmodN E) :
        quotientMap E d (e.symm (e q ⊓ e r)) = quotientMap E d q ∩ quotientMap E d r := by
      induction q using Quotient.ind with
      | _ s =>
        induction r using Quotient.ind with
        | _ t =>
          letI := Gelfand516.enhancedMeasurableSpace E
          have hi : s.val ∩ t.val ∈ E.measurable :=
            (show MeasurableSet s.val from s.property).inter
              (show MeasurableSet t.val from t.property)
          change quotientMap E d
              (e.symm (e (MmodN.mk s.val s.property) ⊓ e (MmodN.mk t.val t.property))) =
            quotientMap E d (MmodN.mk s.val s.property) ∩
              quotientMap E d (MmodN.mk t.val t.property)
          rw [← Gelfand516Compact.class_inter E e s.val t.val s.property t.property hi,
            e.symm_apply_apply]
          exact d.inter s.val t.val s.property t.property
    simpa only [e.apply_symm_apply] using h (e.symm a) (e.symm b)

include d in
theorem exists_booleanSection [Nontrivial B] (e : MmodN E ≃o B) :
    Nonempty (Gelfand516.BooleanSection E e) :=
  exists_booleanSection_of_lowerDensity E e (toLowerDensity E d e)

end EnhancedSetDensity

end Gelfand516Lifting
end
end Gelfand516Source20

/- Source: Work.Gelfand516.Lifting.EnhancedGluing; SHA256 b255451391b915347048aa651922f29162fd00577e95e333a2c59b047d86ecf5. -/
section Gelfand516Source21

set_option autoImplicit false
noncomputable section
open Set GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Lifting
universe u

lemma partialPreimage_empty {X Y : Type u} (f : X → Option Y) :
    partialPreimage f ∅ = ∅ := by
  ext x
  simp [partialPreimage]

lemma partialPreimage_inter {X Y : Type u} (f : X → Option Y) (s t : Set Y) :
    partialPreimage f (s ∩ t) = partialPreimage f s ∩ partialPreimage f t := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy.1, hxy⟩, ⟨y, hy.2, hxy⟩⟩
  · rintro ⟨⟨y, hy, hxy⟩, ⟨z, hz, hxz⟩⟩
    have he : y = z := Option.some.inj (hxy.symm.trans hxz)
    exact ⟨y, ⟨hy, he.symm ▸ hz⟩, hxy⟩

lemma partialPreimage_symmDiff' {X Y : Type u} (f : X → Option Y) (s t : Set Y) :
    partialPreimage f (symmDiff s t) = symmDiff (partialPreimage f s) (partialPreimage f t) :=
  (GelfandVNA.Duality.partialPreimage_symmDiff f s t).symm

/-- Lower densities glue literally along the canonical arbitrary coproduct. -/
def EnhancedSetDensity.coprod {I : Type u} {Y : I → Type u}
    (F : ∀ i, Enhanced (Y i)) (ρ : ∀ i, EnhancedSetDensity (F i)) :
    EnhancedSetDensity (coprodEnhanced F) where
  toFun := fun s => {y | y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' s)}
  measurable := by
    intro s hs i
    exact (ρ i).measurable _ (hs i)
  rep := by
    intro s hs i
    exact (ρ i).rep _ (hs i)
  congr := by
    intro s t hs ht hst
    ext y
    change y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' s) ↔
      y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' t)
    rw [(ρ y.1).congr _ _ (hs y.1) (ht y.1) (hst y.1)]
  empty := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    change y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' ∅) at hy
    rw [preimage_empty, (ρ y.1).empty] at hy
    exact hy
  inter := by
    intro s t hs ht
    ext y
    change y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' (s ∩ t)) ↔
      y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' s) ∧
        y.2 ∈ (ρ y.1).toFun (Sigma.mk y.1 ⁻¹' t)
    rw [preimage_inter, (ρ y.1).inter _ _ (hs y.1) (ht y.1)]
    rfl

/-- Pullback transports a lower density along actual inverse premaps. The
literal round trip supplies equality of all input sets, not just quotient classes. -/
def EnhancedSetDensity.of_inverse_premaps {X Y : Type u}
    {E : Enhanced X} {F : Enhanced Y} (f : Premap E F) (g : Premap F E)
    (hgf : partialCompose g.val f.val = fun x => some x) (ρ : EnhancedSetDensity F) :
    EnhancedSetDensity E := by
  have hround (s : Set X) : partialPreimage f.val (partialPreimage g.val s) = s := by
    rw [← partialPreimage_comp, hgf, partialPreimage_id]
  refine {
    toFun := fun s => partialPreimage f.val (ρ.toFun (partialPreimage g.val s))
    measurable := fun s hs => f.property.2.1 _ (ρ.measurable _ (g.property.2.1 s hs))
    rep := ?_
    congr := ?_
    empty := ?_
    inter := ?_ }
  · intro s hs
    have hn := f.property.2.2 _ (ρ.rep _ (g.property.2.1 s hs))
    rwa [partialPreimage_symmDiff', hround] at hn
  · intro s t hs ht hst
    have hn := g.property.2.2 _ hst
    rw [partialPreimage_symmDiff'] at hn
    rw [ρ.congr _ _ (g.property.2.1 s hs) (g.property.2.1 t ht) hn]
  · rw [partialPreimage_empty, ρ.empty, partialPreimage_empty]
  · intro s t hs ht
    rw [partialPreimage_inter, ρ.inter _ _ (g.property.2.1 s hs) (g.property.2.1 t ht),
      partialPreimage_inter]

/-- Canonical strict localizability assembles component lower densities by
the exact coproduct and literal inverse-premap data from its definition. -/
theorem exists_enhancedSetDensity_of_strictlyLocalizable
    (hfinite : ∀ {X : Type u} (E : Enhanced X), IsSigmaFiniteE E → Nonempty (EnhancedSetDensity E))
    {X : Type u} (E : Enhanced X) (hE : IsStrictlyLocalizable E) :
    Nonempty (EnhancedSetDensity E) := by
  classical
  obtain ⟨I, Y, F, hF, f, g, hgf, hfg⟩ := hE
  let ρ : ∀ i, EnhancedSetDensity (F i) := fun i => (hfinite (F i) (hF i)).some
  exact ⟨EnhancedSetDensity.of_inverse_premaps f g hgf (EnhancedSetDensity.coprod F ρ)⟩

end Gelfand516Lifting
end
end Gelfand516Source21

/- Source: Work.Gelfand516.Lifting.FiniteEnhancedDensity; SHA256 67781e682ea14631aca4740b390da3b81bc5941fa915c7eb8829e14cd84f6bff. -/
section Gelfand516Source22

set_option autoImplicit false
noncomputable section
open Set MeasureTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Lifting
universe u

/-- Canonical sigma-finiteness supplies an actual lower density. The faithful
finite measure has exactly the enhanced null ideal, including all subsets. -/
theorem exists_enhancedSetDensity_of_sigmaFinite {X : Type u} (E : Enhanced X)
    (hE : IsSigmaFiniteE E) : Nonempty (EnhancedSetDensity E) := by
  letI := Gelfand454.measurableSpace E
  obtain ⟨μ, hμ, hnull⟩ := Gelfand454.exists_finiteMeasure E hE
  letI : @IsFiniteMeasure X (Gelfand454.measurableSpace E) μ := hμ
  by_cases hzero : μ univ = 0
  · exact ⟨EnhancedSetDensity.of_null E ((hnull univ).mp hzero)⟩
  · have hcomplete (s : Set X) (hs : μ s = 0) : MeasurableSet s :=
      E.negligibleMeasurable ((hnull s).mp hs)
    obtain ⟨ρ⟩ := exists_setDensity_of_finite_complete μ hcomplete hzero
    exact ⟨enhancedDensityOfSetDensity E μ hnull ρ⟩

/-- The genuine lower-density existence theorem for the exact canonical
strict-localizability predicate. No lifting premise remains. -/
theorem exists_enhancedSetDensity {X : Type u} (E : Enhanced X)
    (hE : IsStrictlyLocalizable E) : Nonempty (EnhancedSetDensity E) :=
  exists_enhancedSetDensity_of_strictlyLocalizable
    (fun E hE => exists_enhancedSetDensity_of_sigmaFinite E hE) E hE

/-- The von Neumann--Maharam Boolean lifting theorem in the exact interface
needed by Proposition5.16. All-null spaces are handled separately by that target. -/
theorem exists_booleanSection_of_strictlyLocalizable {X B : Type u} [BooleanAlgebra B]
    (E : Enhanced X) (e : MmodN E ≃o B) (hE : IsStrictlyLocalizable E)
    (hnonnull : (univ : Set X) ∉ E.negligible) : Nonempty (Gelfand516.BooleanSection E e) := by
  have hm : (univ : Set X) ∈ E.measurable := by
    simpa only [compl_empty] using E.sigmaAlgebra.2.1 ∅ E.sigmaAlgebra.1
  have htop : (⊤ : B) ≠ ⊥ := by
    intro h
    apply hnonnull
    apply (Gelfand516Compact.class_null_iff E e univ hm).mp
    rw [Gelfand516Compact.class_univ E e hm]
    exact h
  letI : Nontrivial B := nontrivial_of_ne ⊤ ⊥ htop
  obtain ⟨d⟩ := exists_enhancedSetDensity E hE
  exact EnhancedSetDensity.exists_booleanSection E d e

end Gelfand516Lifting
end
end Gelfand516Source22

/- Source: Work.Gelfand516.CompactInverse; SHA256 8d8255e818f16fe7667ea98e23c15a8c57c7589d5b6ea35c79059dcb06ad0f6b. -/
section Gelfand516Source23

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Compact
open Gelfand516
universe u
variable {X B : Type u} [BooleanAlgebra B]
variable (E : Enhanced X) (e : MmodN E ≃o B)
variable (K : Set (Set X)) (hKM : ∀ k ∈ K, k ∈ E.measurable)

/-- A spectrum point selects a family in the compact class with the finite
intersection property, including the empty finite intersection. -/
theorem compact_point_exists (hKC : IsCompactClassOn univ K) (p : stoneSpectrum B) :
    ∃ x : X, ∀ k (hk : k ∈ K), p ∈ basic (e (MmodN.mk k (hKM k hk))) → x ∈ k := by
  classical
  letI := enhancedMeasurableSpace E
  have hum : (univ : Set X) ∈ E.measurable := by
    simpa only [compl_empty] using E.sigmaAlgebra.2.1 ∅ E.sigmaAlgebra.1
  let T : Set (Set X) := {k | ∃ hk : k ∈ K, p ∈ basic (e (MmodN.mk k (hKM k hk)))}
  have hTK : T ⊆ K := fun _ ⟨hk, _⟩ => hk
  have hfinite (U : Set (Set X)) (hU : U.Finite) (hUT : U ⊆ T) :
      ∃ hm : ⋂₀ U ∈ E.measurable, p ∈ basic (e (MmodN.mk (⋂₀ U) hm)) := by
    induction U, hU using Set.Finite.induction_on with
    | empty =>
      have hm : ⋂₀ (∅ : Set (Set X)) ∈ E.measurable := by
        rw [sInter_empty]
        exact hum
      refine ⟨hm, ?_⟩
      have he : e (MmodN.mk (⋂₀ (∅ : Set (Set X))) hm) = ⊤ := by
        simpa only [sInter_empty] using class_univ E e hum
      rw [he, basic_top]
      trivial
    | @insert k U hkU hU ih =>
      obtain ⟨hkK, hpk⟩ := hUT (mem_insert k U)
      obtain ⟨hm, hpU⟩ := ih (fun _ hx => hUT (mem_insert_of_mem _ hx))
      have hm' : ⋂₀ (insert k U) ∈ E.measurable := by
        rw [sInter_insert]
        exact (show MeasurableSet k from hKM k hkK).inter (show MeasurableSet (⋂₀ U) from hm)
      refine ⟨hm', ?_⟩
      have he : e (MmodN.mk (⋂₀ (insert k U)) hm') =
          e (MmodN.mk k (hKM k hkK)) ⊓ e (MmodN.mk (⋂₀ U) hm) := by
        simpa only [sInter_insert] using class_inter E e k (⋂₀ U) (hKM k hkK) hm
          ((show MeasurableSet k from hKM k hkK).inter (show MeasurableSet (⋂₀ U) from hm))
      rw [he, basic_inf]
      exact ⟨hpk, hpU⟩
  have hFIP : ∀ U : Set (Set X), U.Finite → U ⊆ T → (univ ∩ ⋂₀ U).Nonempty := by
    intro U hU hUT
    obtain ⟨hm, hp⟩ := hfinite U hU hUT
    have hN : ⋂₀ U ∉ E.negligible := by
      intro hn
      rw [(class_null_iff E e _ hm).2 hn, basic_bot] at hp
      exact hp
    have hn : (⋂₀ U).Nonempty := by
      by_contra h
      exact hN (by rw [not_nonempty_iff_eq_empty.mp h]; exact E.sigmaIdeal.1)
    simpa only [univ_inter] using hn
  obtain ⟨x, hx⟩ := hKC T hTK hFIP
  exact ⟨x, fun k hk hp => mem_sInter.mp hx.2 k ⟨hk, hp⟩⟩

def innerOpen (s : Set X) : Set (stoneSpectrum B) :=
  ⋃ k : {k : Set X // k ∈ K ∧ k ⊆ s}, basic (e (MmodN.mk k.1 (hKM k.1 k.2.1)))

theorem innerOpen_isOpen (s : Set X) : IsOpen (innerOpen E e K hKM s) :=
  isOpen_iUnion (fun _ => basic_isOpen _)

theorem innerOpen_subset_basic (s : Set X) (hs : s ∈ E.measurable) :
    innerOpen E e K hKM s ⊆ basic (e (MmodN.mk s hs)) := by
  intro p hp
  unfold innerOpen at hp
  obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
  exact basic_mono (class_mono E e (hKM k.1 k.2.1) hs k.2.2) hpk

theorem closure_innerOpen (hinner : ∀ s : Set X, s ∈ E.measurable → s ∉ E.negligible →
    ∃ k ∈ K, k ⊆ s ∧ k ∉ E.negligible) (s : Set X) (hs : s ∈ E.measurable) :
    closure (innerOpen E e K hKM s) = basic (e (MmodN.mk s hs)) := by
  classical
  letI := enhancedMeasurableSpace E
  apply subset_antisymm
    (closure_minimal (innerOpen_subset_basic E e K hKM s hs) (basic_isClosed _))
  intro p hp
  by_contra hpC
  obtain ⟨c, hpc, hc⟩ := exists_basic_of_mem_open
    (show p ∈ basic (e (MmodN.mk s hs)) ∩ (closure (innerOpen E e K hKM s))ᶜ from ⟨hp, hpC⟩)
    ((basic_isOpen _).inter isClosed_closure.isOpen_compl)
  have hcb : c ≤ e (MmodN.mk s hs) := basic_subset_iff.mp (fun _ hx => (hc hx).1)
  have hc0 : c ≠ ⊥ := by
    intro h
    simpa only [h, basic_bot, mem_empty_iff_false] using hpc
  obtain ⟨r, hr⟩ := Quotient.exists_rep (e.symm c)
  have hrc : e (MmodN.mk r.1 r.2) = c := (congrArg e hr).trans (e.apply_symm_apply c)
  have hrsm : r.1 ∩ s ∈ E.measurable :=
    (show MeasurableSet r.1 from r.2).inter (show MeasurableSet s from hs)
  have hrsN : r.1 ∩ s ∉ E.negligible := by
    intro hn
    apply hc0
    have he := (class_null_iff E e _ hrsm).2 hn
    rw [class_inter E e r.1 s r.2 hs hrsm, hrc, inf_eq_left.mpr hcb] at he
    exact he
  obtain ⟨k, hkK, hks, hkN⟩ := hinner (r.1 ∩ s) hrsm hrsN
  have hk0 : e (MmodN.mk k (hKM k hkK)) ≠ ⊥ := by
    exact fun h => hkN ((class_null_iff E e k (hKM k hkK)).1 h)
  obtain ⟨q, hqk⟩ := basic_nonempty hk0
  have hqc : q ∈ basic c := by
    rw [← hrc]
    exact basic_mono (class_mono E e (hKM k hkK) r.2 (hks.trans inter_subset_left)) hqk
  have hqV : q ∈ innerOpen E e K hKM s := by
    exact mem_iUnion.mpr ⟨⟨k, hkK, hks.trans inter_subset_right⟩, hqk⟩
  exact (hc hqc).2 (subset_closure hqV)

theorem realization_pullback (hinner : ∀ s : Set X, s ∈ E.measurable → s ∉ E.negligible →
    ∃ k ∈ K, k ⊆ s ∧ k ∉ E.negligible)
    (ψ : stoneSpectrum B → X)
    (hψ : ∀ p k (hk : k ∈ K), p ∈ basic (e (MmodN.mk k (hKM k hk))) → ψ p ∈ k)
    (s : Set X) (hs : s ∈ E.measurable) :
    IsMeagre (symmDiff (ψ ⁻¹' s) (basic (e (MmodN.mk s hs)))) := by
  have hinside (t : Set X) : innerOpen E e K hKM t ⊆ ψ ⁻¹' t := by
    intro p hp
    unfold innerOpen at hp
    obtain ⟨k, hpk⟩ := Set.mem_iUnion.mp hp
    exact k.2.2 (hψ p k.1 k.2.1 hpk)
  have hboundary (t : Set X) (ht : t ∈ E.measurable) :
      IsMeagre (symmDiff (basic (e (MmodN.mk t ht))) (innerOpen E e K hKM t)) := by
    rw [← closure_innerOpen E e K hKM hinner t ht]
    exact (isMeagre_symmDiff_iff _ _).mpr
      (closure_residualEq (innerOpen_isOpen E e K hKM t).isLocallyClosed)
  apply IsMeagre.mono _ ((hboundary s hs).union (hboundary sᶜ (E.sigmaAlgebra.2.1 s hs)))
  intro p hp
  rw [class_compl E e s hs, basic_compl]
  simp only [mem_symmDiff, mem_sdiff, mem_union, mem_compl_iff] at hp ⊢
  rcases hp with ⟨hps, hpb⟩ | ⟨hpb, hps⟩
  · exact Or.inr (Or.inl ⟨hpb, fun hv => (hinside sᶜ hv) hps⟩)
  · exact Or.inl (Or.inl ⟨hpb, fun hv => hps (hinside s hv)⟩)

/-- Compactness alone realizes the inverse map, with the canonical measurable
and negligible pullback clauses. No Boolean lifting is assumed. -/
theorem exists_compact_inverse_premap (hcompact : IsCompactEnhancedOn E univ) :
    ∃ ψ : Premap (TM (stoneSpectrum B)) E,
      ∀ s (hs : s ∈ E.measurable),
        IsMeagre (symmDiff (partialPreimage ψ.val s) (basic (e (MmodN.mk s hs)))) := by
  classical
  obtain ⟨K, hKM', hKC, hinner'⟩ := hcompact
  let hKM : ∀ k ∈ K, k ∈ E.measurable := fun k hk => (hKM' k hk).2
  have hinner : ∀ s : Set X, s ∈ E.measurable → s ∉ E.negligible →
      ∃ k ∈ K, k ⊆ s ∧ k ∉ E.negligible :=
    fun s hs hn => hinner' s (subset_univ _) hs hn
  choose ψ hψ using compact_point_exists E e K hKM hKC
  have hpull (s : Set X) (hs : s ∈ E.measurable) :=
    realization_pullback E e K hKM hinner ψ hψ s hs
  have hpre (s : Set X) : partialPreimage (fun p => some (ψ p)) s = ψ ⁻¹' s := by
    ext p
    simp [partialPreimage]
  refine ⟨⟨fun p => some (ψ p), ?_⟩, ?_⟩
  · refine ⟨?_, fun s hs => ?_, fun s hn => ?_⟩
    · have he : (partialDomain (fun p => some (ψ p)))ᶜ = ∅ := by
        ext p
        simp [partialDomain]
      rw [he]
      exact IsMeagre.empty
    · rw [hpre]
      exact ⟨basic (e (MmodN.mk s hs)), basic_isOpen _, hpull s hs⟩
    · rw [hpre]
      have hs := E.negligibleMeasurable hn
      have h := hpull s hs
      rw [(class_null_iff E e s hs).2 hn, basic_bot] at h
      have he : symmDiff (ψ ⁻¹' s) ∅ = ψ ⁻¹' s := by
        ext p
        simp only [Set.mem_symmDiff, Set.mem_empty_iff_false, not_false_eq_true,
          and_true, false_and, or_false]
      rw [he] at h
      exact h
  · intro s hs
    change IsMeagre (symmDiff (partialPreimage (fun p => some (ψ p)) s) _)
    rw [hpre]
    exact hpull s hs

end Gelfand516Compact
end
end Gelfand516Source23

/- Source: Work.Gelfand516.LocalizableHulls; SHA256 064005c44fcd8a3d14811123d5c28f9a2663214448c4ab6d621560c691d54844. -/
section Gelfand516Source24

set_option autoImplicit false
noncomputable section
open Set MeasureTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516
universe u

/-- Finite ordinary measure envelopes have the required null-part property. -/
theorem hasMeasurableHulls_of_sigmaFinite {X : Type u} (E : Enhanced X)
    (hE : IsSigmaFiniteE E) : HasMeasurableHulls E := by
  letI := Gelfand454.measurableSpace E
  obtain ⟨μ, hμ, hnull⟩ := Gelfand454.exists_finiteMeasure E hE
  letI : @IsFiniteMeasure X (Gelfand454.measurableSpace E) μ := hμ
  intro s
  have hsm : toMeasurable μ s ∈ E.measurable :=
    show MeasurableSet (toMeasurable μ s) from measurableSet_toMeasurable μ s
  refine ⟨toMeasurable μ s, hsm, subset_toMeasurable _ _, ?_⟩
  intro m hm hms hdis
  apply (hnull m).mp
  have h := Measure.measure_toMeasurable_inter (show MeasurableSet m from hm) (measure_ne_top μ s)
  rw [inter_eq_right.mpr hms, Set.disjoint_iff_inter_eq_empty.mp hdis.symm, measure_empty] at h
  exact h

/-- The envelope property is componentwise for the exact canonical coproduct. -/
theorem hasMeasurableHulls_coprod {I : Type u} {Y : I → Type u}
    (F : ∀ i, Enhanced (Y i)) (hF : ∀ i, HasMeasurableHulls (F i)) :
    HasMeasurableHulls (coprodEnhanced F) := by
  classical
  intro s
  choose H hm hsub hmax using fun i => hF i (Sigma.mk i ⁻¹' s)
  let W : Set (Σ i, Y i) := {y | y.2 ∈ H y.1}
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    exact hm i
  · intro y hy
    exact hsub y.1 hy
  · intro m hmm hmW hdis i
    apply hmax i (Sigma.mk i ⁻¹' m) (hmm i)
    · intro y hy
      exact hmW hy
    · apply Set.disjoint_left.mpr
      intro y hym hys
      exact Set.disjoint_left.mp hdis hym hys

/-- Literal inverse premaps transport measurable envelopes without choosing a
total representative or replacing the canonical equivalence relation. -/
theorem hasMeasurableHulls_of_inverse_premaps {X Y : Type u}
    {E : Enhanced X} {F : Enhanced Y} (f : Premap E F) (g : Premap F E)
    (hgf : partialCompose g.val f.val = fun x => some x)
    (hfg : partialCompose f.val g.val = fun y => some y)
    (hF : HasMeasurableHulls F) : HasMeasurableHulls E := by
  have hroundE (s : Set X) : partialPreimage f.val (partialPreimage g.val s) = s := by
    rw [← partialPreimage_comp, hgf, partialPreimage_id]
  have hroundF (s : Set Y) : partialPreimage g.val (partialPreimage f.val s) = s := by
    rw [← partialPreimage_comp, hfg, partialPreimage_id]
  have hmono {A C : Type u} (p : A → Option C) {s t : Set C} (h : s ⊆ t) :
      partialPreimage p s ⊆ partialPreimage p t := by
    rintro a ⟨c, hc, hp⟩
    exact ⟨c, h hc, hp⟩
  intro s
  obtain ⟨H, hHm, hsH, hH⟩ := hF (partialPreimage g.val s)
  refine ⟨partialPreimage f.val H, f.property.2.1 _ hHm, ?_, ?_⟩
  · rw [← hroundE s]
    exact hmono f.val hsH
  · intro m hmm hmH hdis
    have hmH' : partialPreimage g.val m ⊆ H := by
      simpa only [hroundF H] using hmono g.val hmH
    have hd : Disjoint (partialPreimage g.val m) (partialPreimage g.val s) := by
      apply Set.disjoint_left.mpr
      rintro y ⟨x, hxm, hgx⟩ ⟨z, hzs, hgz⟩
      have hxz : x = z := Option.some.inj (hgx.symm.trans hgz)
      exact Set.disjoint_left.mp hdis hxm (hxz.symm ▸ hzs)
    have hn := hH _ (g.property.2.1 _ hmm) hmH' hd
    simpa only [hroundE m] using f.property.2.2 _ hn

theorem hasMeasurableHulls_of_strictlyLocalizable {X : Type u} (E : Enhanced X)
    (hE : IsStrictlyLocalizable E) : HasMeasurableHulls E := by
  obtain ⟨I, Y, F, hF, f, g, hgf, hfg⟩ := hE
  exact hasMeasurableHulls_of_inverse_premaps f g hgf hfg
    (hasMeasurableHulls_coprod F (fun i => hasMeasurableHulls_of_sigmaFinite (F i) (hF i)))

/-- The forward premap needed by Proposition5.16, with only the genuine
Boolean-lifting existence still assumed explicitly. -/
def liftedPremap {X B : Type u} [CompleteBooleanAlgebra B]
    {E : Enhanced X} {e : MmodN E ≃o B}
    (hE : IsStrictlyLocalizable E) (θ : BooleanSection E e) :
    Premap E (TM (stoneSpectrum B)) :=
  sectionPremap θ (hasMeasurableHulls_of_strictlyLocalizable E hE)

end Gelfand516
end
end Gelfand516Source24

/- Source: Work.Gelfand516.CompactInverseEquivalence; SHA256 67501444f6b7e510f2d86fd840485eb100ae5f4dd915d5a54ca33eb9deed0063. -/
section Gelfand516Source25

set_option autoImplicit false
noncomputable section
open Set CategoryTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Compact
open Gelfand516
universe u

theorem negligible_symmDiff_trans {X : Type u} (E : Enhanced X) {a b c : Set X}
    (hab : symmDiff a b ∈ E.negligible) (hbc : symmDiff b c ∈ E.negligible) :
    symmDiff a c ∈ E.negligible := by
  apply negligible_mono E _ (negligible_union E hab hbc)
  intro x hx
  simp only [mem_symmDiff, mem_union, mem_sdiff] at hx ⊢
  tauto

theorem premap_preimage_symmDiff_negligible {X Y : Type u}
    {E : Enhanced X} {F : Enhanced Y} (f : Premap E F) {a b : Set Y}
    (h : symmDiff a b ∈ F.negligible) :
    symmDiff (partialPreimage f.val a) (partialPreimage f.val b) ∈ E.negligible := by
  change (partialPreimage f.val a \ partialPreimage f.val b) ∪
    (partialPreimage f.val b \ partialPreimage f.val a) ∈ E.negligible
  rw [partialPreimage_symmDiff]
  exact f.property.2.2 _ h

/-- Conditional form of Proposition5.16: the supplied Boolean lifting gives
the forward map, compactness gives an actual inverse map, and both composites
are proved weakly equal to the identities. Lifting existence is not asserted. -/
theorem ems_iso_of_booleanSection {X B : Type u} [CompleteBooleanAlgebra B]
    (E : Enhanced X) (e : MmodN E ≃o B)
    (hcompact : IsCompactEnhancedOn E univ) (hstrict : IsStrictlyLocalizable E)
    (θ : BooleanSection E e) :
    Nonempty (EMS.of X E ≅ EMS.of (stoneSpectrum B) (TM (stoneSpectrum B))) := by
  classical
  let η := liftedPremap hstrict θ
  obtain ⟨ψ, hψ⟩ := exists_compact_inverse_premap E e hcompact
  have hηbasic (b : B) : partialPreimage η.val (basic b) = θ.toHom b :=
    sectionPremap_basic θ (hasMeasurableHulls_of_strictlyLocalizable E hstrict) b
  have hfirst : weakHomRelation E E (compPremap η ψ) (idPremap E) := by
    intro s hs
    change symmDiff (partialPreimage (partialCompose ψ.val η.val) s)
      (partialPreimage (fun x => some x) s) ∈ E.negligible
    rw [partialPreimage_comp, partialPreimage_id]
    have h1 := premap_preimage_symmDiff_negligible η (hψ s hs)
    have h2 : symmDiff (partialPreimage η.val (basic (e (MmodN.mk s hs)))) s ∈ E.negligible := by
      rw [hηbasic, symmDiff_comm]
      simpa only [sectionPoint_preimage_basic] using sectionPoint_preimage_rep θ s hs
    exact negligible_symmDiff_trans E h1 h2
  have hsecond : weakHomRelation (TM (stoneSpectrum B)) (TM (stoneSpectrum B))
      (compPremap ψ η) (idPremap (TM (stoneSpectrum B))) := by
    intro t ht
    obtain ⟨b, hb⟩ := baire_basic_rep θ ht
    change symmDiff (partialPreimage (partialCompose η.val ψ.val) t)
      (partialPreimage (fun p => some p) t) ∈ (TM (stoneSpectrum B)).negligible
    rw [partialPreimage_id]
    have h1 := premap_preimage_symmDiff_negligible (compPremap ψ η) hb
    have h2 : symmDiff (partialPreimage (partialCompose η.val ψ.val) (basic b))
        (basic b) ∈ (TM (stoneSpectrum B)).negligible := by
      rw [partialPreimage_comp, hηbasic]
      change IsMeagre (symmDiff (partialPreimage ψ.val (θ.toHom b)) (basic b))
      simpa only [θ.quotient_section] using hψ (θ.toHom b) (θ.measurable b)
    have h3 : symmDiff (basic b) t ∈ (TM (stoneSpectrum B)).negligible := by
      rw [symmDiff_comm]
      exact hb
    exact negligible_symmDiff_trans _ (negligible_symmDiff_trans _ h1 h2) h3
  refine ⟨{
    hom := Quot.mk _ η
    inv := Quot.mk _ ψ
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · exact Quot.sound hfirst
  · exact Quot.sound hsecond

end Gelfand516Compact
end
end Gelfand516Source25

/- Source: Work.Gelfand516.CompactInverseNull; SHA256 fa1b2842eb54e76fc404d583ccd5f1e8e9b1bac8ad90b84b1c6b7ff1e55d29f5. -/
section Gelfand516Source26

set_option autoImplicit false
noncomputable section
open Set CategoryTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Compact
open Gelfand516
universe u
variable {X B : Type u} [BooleanAlgebra B]

/-- The entirely negligible case has an empty spectrum, even when X itself
is nonempty. This is the reason the forward premap must be allowed to be partial. -/
theorem spectrum_isEmpty_of_null (E : Enhanced X) (e : MmodN E ≃o B)
    (hnull : (univ : Set X) ∈ E.negligible) : IsEmpty (stoneSpectrum B) := by
  have hm := E.negligibleMeasurable hnull
  have htop : (⊤ : B) = ⊥ :=
    (class_univ E e hm).symm.trans ((class_null_iff E e univ hm).2 hnull)
  refine ⟨fun p => ?_⟩
  have h := congrArg (fun b => (show BoundedLatticeHom B Bool from p) b) htop
  rw [map_top, map_bot] at h
  change true = false at h
  cases h

theorem ems_iso_of_null (E : Enhanced X) (e : MmodN E ≃o B)
    (hnull : (univ : Set X) ∈ E.negligible) :
    Nonempty (EMS.of X E ≅ EMS.of (stoneSpectrum B) (TM (stoneSpectrum B))) := by
  letI := spectrum_isEmpty_of_null E e hnull
  have hneg (s : Set (stoneSpectrum B)) : s ∈ (TM (stoneSpectrum B)).negligible := by
    change IsMeagre s
    apply IsMeagre.mono _ IsMeagre.empty
    intro p hp
    exact isEmptyElim p
  have hmeas (s : Set (stoneSpectrum B)) : s ∈ (TM (stoneSpectrum B)).measurable :=
    (TM (stoneSpectrum B)).negligibleMeasurable (hneg s)
  let η : Premap E (TM (stoneSpectrum B)) := ⟨fun _ => none, by
    have hp (s : Set (stoneSpectrum B)) : partialPreimage (fun _ : X => none) s = ∅ := by
      ext x
      simp [partialPreimage]
    refine ⟨?_, fun s hs => ?_, fun s hs => ?_⟩
    · have hd : (partialDomain (fun _ : X => (none : Option (stoneSpectrum B))))ᶜ = univ := by
        ext x
        simp [partialDomain]
      rwa [hd]
    · rw [hp]
      exact E.sigmaAlgebra.1
    · rw [hp]
      exact E.sigmaIdeal.1⟩
  let ψ : Premap (TM (stoneSpectrum B)) E := ⟨fun p => isEmptyElim p, by
    exact ⟨hneg _, fun s hs => hmeas _, fun s hs => hneg _⟩⟩
  have hfirst : weakHomRelation E E (compPremap η ψ) (idPremap E) := by
    intro s hs
    exact negligible_mono E (subset_univ _) hnull
  have hsecond : weakHomRelation (TM (stoneSpectrum B)) (TM (stoneSpectrum B))
      (compPremap ψ η) (idPremap (TM (stoneSpectrum B))) := by
    intro s hs
    exact hneg _
  exact ⟨{
    hom := Quot.mk _ η
    inv := Quot.mk _ ψ
    hom_inv_id := Quot.sound hfirst
    inv_hom_id := Quot.sound hsecond }⟩

/-- All of the object-level construction is reduced to Boolean lifting on the
non-null branch. This is an explicit hypothesis, not an asserted theorem. -/
theorem ems_iso_of_lifting_on_nonnull {Y C : Type u} [CompleteBooleanAlgebra C]
    (E : Enhanced Y) (e : MmodN E ≃o C)
    (hcompact : IsCompactEnhancedOn E univ) (hstrict : IsStrictlyLocalizable E)
    (hlift : (univ : Set Y) ∉ E.negligible → Nonempty (BooleanSection E e)) :
    Nonempty (EMS.of Y E ≅ EMS.of (stoneSpectrum C) (TM (stoneSpectrum C))) := by
  classical
  by_cases hn : (univ : Set Y) ∈ E.negligible
  · exact ems_iso_of_null E e hn
  · obtain ⟨θ⟩ := hlift hn
    exact ems_iso_of_booleanSection E e hcompact hstrict θ

end Gelfand516Compact
end
end Gelfand516Source26

/- Source: Work.Gelfand454.CountableSup; SHA256 10d40bdcf51322e0247d71b04e9590167eb75ee93db7bdce686e680ea29061a2. -/
section Gelfand516Source27

open Set QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand454
universe u
variable {X : Type u} (E : Enhanced X)

theorem mk_le_mk {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
    MmodN.mk a ha ≤ MmodN.mk b hb ↔ a \ b ∈ E.negligible := Iff.rfl

theorem mk_mono {a b : Set X} (ha : a ∈ E.measurable) (hb : b ∈ E.measurable)
    (hab : a ⊆ b) : MmodN.mk a ha ≤ MmodN.mk b hb := by
  change a \ b ∈ E.negligible
  simpa only [Set.diff_eq_empty.mpr hab] using E.sigmaIdeal.1

/-- Countable unions are actual least upper bounds in the exact canonical quotient. -/
theorem mk_iUnion_isLUB (a : ℕ → Set X) (ha : ∀ n, a n ∈ E.measurable) :
    IsLUB (Set.range fun n => MmodN.mk (a n) (ha n))
      (MmodN.mk (⋃ n, a n) (E.sigmaAlgebra.2.2 a ha)) := by
  constructor
  · rintro q ⟨n, rfl⟩
    exact mk_mono E (ha n) _ (Set.subset_iUnion a n)
  · intro q hq
    induction q using Quotient.ind with
    | _ b =>
      change (⋃ n, a n) \ b.1 ∈ E.negligible
      rw [Set.iUnion_diff]
      apply E.sigmaIdeal.2.2
      intro n
      exact hq (Set.mem_range_self n)

theorem exists_lub_sequence (a : ℕ → MmodN E) :
    ∃ q, IsLUB (Set.range a) q := by
  classical
  let r (n : ℕ) := (a n).out
  have heq (n : ℕ) : MmodN.mk (r n).1 (r n).2 = a n := Quotient.out_eq _
  refine ⟨MmodN.mk (⋃ n, (r n).1) (E.sigmaAlgebra.2.2 _ fun n => (r n).2), ?_⟩
  have h := mk_iUnion_isLUB E (fun n => (r n).1) (fun n => (r n).2)
  simpa only [heq] using h

/-- No measure hypothesis is needed for sigma-completeness of M/N. -/
theorem exists_lub_countable (s : Set (MmodN E)) (hs : s.Countable) :
    ∃ q, IsLUB s q := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨MmodN.mk ∅ E.sigmaAlgebra.1, ?_, ?_⟩
    · simp
    · intro q _
      induction q using Quotient.ind with
      | _ b => exact mk_mono E _ b.2 (Set.empty_subset _)
  · obtain ⟨a, rfl⟩ := hs.exists_eq_range hne
    exact exists_lub_sequence E a

end Gelfand454
end Gelfand516Source27

/- Source: Work.Gelfand454.CompleteOrder; SHA256 9c872b2d96040b0f50a4b924f8aa2c564a37324604659b513267a0a95fbe483a. -/
section Gelfand516Source28

open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand454
universe u
variable {X : Type u} (E : Enhanced X)

theorem mk_out (a : MmodN E) : MmodN.mk a.out.1 a.out.2 = a := Quotient.out_eq _

/-- The countable essential-union theorem gives arbitrary suprema in the
canonical quotient, with no replacement of its order or equivalence relation. -/
theorem exists_lub_of_finiteMeasure
    (ν : @Measure X (measurableSpace E)) [IsFiniteMeasure ν]
    (hnull : ∀ s : Set X, ν s = 0 ↔ s ∈ E.negligible)
    (S : Set (MmodN E)) : ∃ a, IsLUB S a := by
  letI := measurableSpace E
  let C : Set (Set X) := (fun q : MmodN E => q.out.1) '' S
  have hC : ∀ s ∈ C, MeasurableSet s := by
    rintro s ⟨q, hq, rfl⟩
    exact q.out.2
  obtain ⟨D, hDC, hDc, hD⟩ := ν.exists_ae_subset_biUnion_countable hC
  have hDm : MeasurableSet (⋃₀ D) := MeasurableSet.sUnion hDc (fun s hs => hC s (hDC hs))
  refine ⟨MmodN.mk (⋃₀ D) hDm, ?_, ?_⟩
  · intro q hq
    rw [← mk_out E q]
    exact (hnull _).1 (ae_le_set.1 (hD _ ⟨q, hq, rfl⟩))
  · intro b hb
    induction b using Quotient.ind with
    | _ b =>
      change (⋃₀ D) \ b.1 ∈ E.negligible
      apply (hnull _).1
      rw [Set.sUnion_eq_biUnion]
      simp_rw [Set.iUnion_sdiff]
      apply (measure_biUnion_null_iff hDc).2
      intro t ht
      obtain ⟨q, hq, rfl⟩ := hDC ht
      apply (hnull _).2
      have h := hb hq
      rwa [← mk_out E q] at h

theorem exists_lub_of_sigmaFinite (hE : IsSigmaFiniteE E) (S : Set (MmodN E)) :
    ∃ a, IsLUB S a := by
  obtain ⟨ν, hν, hnull⟩ := exists_finiteMeasure E hE
  letI := hν
  exact exists_lub_of_finiteMeasure E ν hnull S

/-- A complete lattice on exactly the canonical quotient and order. -/
@[instance_reducible] noncomputable def quotientCompleteLattice (hE : IsSigmaFiniteE E) :
    CompleteLattice (MmodN E) := by
  classical
  letI : SupSet (MmodN E) := ⟨fun S => (exists_lub_of_sigmaFinite E hE S).choose⟩
  exact completeLatticeOfSup (MmodN E)
    (fun S => (exists_lub_of_sigmaFinite E hE S).choose_spec)

end Gelfand454
end Gelfand516Source28

/- Source: Work.Gelfand454.BooleanAlgebra; SHA256 583bafcc4c764a937010ef3262bd2cc29e8217f1bbd1a649f0a22ce09df57cef. -/
section Gelfand516Source29

open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand454
universe u

/-- The canonical quotient of a sigma-finite enhanced space is a complete
Boolean algebra. Every finite operation is induced by the corresponding set operation. -/
@[instance_reducible] noncomputable def quotientCompleteBooleanAlgebra
    {X : Type u} (E : Enhanced X) (hE : IsSigmaFiniteE E) :
    CompleteBooleanAlgebra (MmodN E) := by
  letI := measurableSpace E
  letI := quotientCompleteLattice E hE
  have hU (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
      a ∪ b ∈ E.measurable := (show MeasurableSet a from ha).union (show MeasurableSet b from hb)
  have hI (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
      a ∩ b ∈ E.measurable := (show MeasurableSet a from ha).inter (show MeasurableSet b from hb)
  have hSup (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
      MmodN.mk (a ∪ b) (hU a b ha hb) = MmodN.mk a ha ⊔ MmodN.mk b hb := by
    apply le_antisymm
    · generalize hq : MmodN.mk a ha ⊔ MmodN.mk b hb = q
      have hqa : MmodN.mk a ha ≤ q := hq ▸ le_sup_left
      have hqb : MmodN.mk b hb ≤ q := hq ▸ le_sup_right
      induction q using Quotient.ind with
      | _ c =>
        change (a ∪ b) \ c.1 ∈ E.negligible
        rw [Set.union_sdiff_distrib]
        exact negligible_union E hqa hqb
    · exact sup_le (mk_mono E ha _ Set.subset_union_left)
        (mk_mono E hb _ Set.subset_union_right)
  have hInf (a b : Set X) (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) :
      MmodN.mk (a ∩ b) (hI a b ha hb) = MmodN.mk a ha ⊓ MmodN.mk b hb := by
    apply le_antisymm
    · exact le_inf (mk_mono E _ ha Set.inter_subset_left)
        (mk_mono E _ hb Set.inter_subset_right)
    · generalize hq : MmodN.mk a ha ⊓ MmodN.mk b hb = q
      have hqa : q ≤ MmodN.mk a ha := hq ▸ inf_le_left
      have hqb : q ≤ MmodN.mk b hb := hq ▸ inf_le_right
      induction q using Quotient.ind with
      | _ c =>
        change c.1 \ (a ∩ b) ∈ E.negligible
        rw [Set.sdiff_inter]
        exact negligible_union E hqa hqb
  have hBot : MmodN.mk ∅ E.sigmaAlgebra.1 = (⊥ : MmodN E) := by
    apply le_antisymm _ bot_le
    generalize hq : (⊥ : MmodN E) = q
    induction q using Quotient.ind with
    | _ b => exact mk_mono E _ b.2 (Set.empty_subset _)
  have huniv : (Set.univ : Set X) ∈ E.measurable := by
    simpa only [Set.compl_empty] using E.sigmaAlgebra.2.1 ∅ E.sigmaAlgebra.1
  have hTop : MmodN.mk (E := E) Set.univ huniv =
      (⊤ : MmodN E) := by
    apply le_antisymm le_top
    generalize hq : (⊤ : MmodN E) = q
    induction q using Quotient.ind with
    | _ b => exact mk_mono E b.2 _ (Set.subset_univ _)
  let c (a : MmodN E) := MmodN.mk a.out.1ᶜ (E.sigmaAlgebra.2.1 _ a.out.2)
  exact {
    toCompleteLattice := quotientCompleteLattice E hE
    compl := c
    le_sup_inf := by
      intro a b d
      induction a using Quotient.ind with
      | _ a =>
        induction b using Quotient.ind with
        | _ b =>
          induction d using Quotient.ind with
          | _ d =>
            change (MmodN.mk a.1 a.2 ⊔ MmodN.mk b.1 b.2) ⊓
              (MmodN.mk a.1 a.2 ⊔ MmodN.mk d.1 d.2) ≤
              MmodN.mk a.1 a.2 ⊔ MmodN.mk b.1 b.2 ⊓ MmodN.mk d.1 d.2
            rw [← hSup, ← hSup, ← hInf, ← hInf, ← hSup]
            apply mk_mono E
            exact (Set.union_inter_distrib_left _ _ _).ge
    inf_compl_le_bot := by
      intro a
      have h := hInf a.out.1 a.out.1ᶜ a.out.2 (E.sigmaAlgebra.2.1 _ a.out.2)
      rw [mk_out E a] at h
      change a ⊓ MmodN.mk a.out.1ᶜ _ ≤ ⊥
      rw [← h]
      simpa only [Set.inter_compl_self] using hBot.le
    top_le_sup_compl := by
      intro a
      have h := hSup a.out.1 a.out.1ᶜ a.out.2 (E.sigmaAlgebra.2.1 _ a.out.2)
      rw [mk_out E a] at h
      change ⊤ ≤ a ⊔ MmodN.mk a.out.1ᶜ _
      rw [← h]
      simpa only [Set.union_compl_self] using hTop.ge
  }

end Gelfand454
end Gelfand516Source29

/- Source: Work.Gelfand454.CoprodIso; SHA256 be7d406710e03f660dbd5a1802ea35efda7c221f145290ad4b480f1aa38f0a68. -/
section Gelfand516Source30

set_option autoImplicit false
noncomputable section
open Set QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
namespace Gelfand454Coprod
universe u
variable {I : Type u} {Y : I → Type u} (F : ∀ i, Enhanced (Y i))

def toFibres : MmodN (coprodEnhanced F) → ∀ i, MmodN (F i) :=
  Quotient.lift (fun m i => MmodN.mk (Sigma.mk i ⁻¹' m.val) (m.property i)) (by
    intro a b hab
    funext i
    apply Quotient.sound
    change (Sigma.mk i ⁻¹' a.val \ Sigma.mk i ⁻¹' b.val) ∪
      (Sigma.mk i ⁻¹' b.val \ Sigma.mk i ⁻¹' a.val) ∈ (F i).negligible
    change ∀ j, Sigma.mk j ⁻¹' ((a.val \ b.val) ∪ (b.val \ a.val)) ∈ (F j).negligible at hab
    simpa only [Set.preimage_union,Set.preimage_sdiff] using hab i)

def fromFibres (a : ∀ i, MmodN (F i)) : MmodN (coprodEnhanced F) :=
  MmodN.mk {p | p.2 ∈ (a p.1).out.val} (fun i => (a i).out.property)

theorem to_from (a : ∀ i, MmodN (F i)) : toFibres F (fromFibres F a) = a := by
  funext i
  change Quotient.mk (nullSetoid (F i)) (a i).out = a i
  exact Quotient.out_eq _

theorem toFibres_injective : Function.Injective (toFibres F) := by
  intro a b
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      intro h
      apply Quotient.sound
      change ∀ i, Sigma.mk i ⁻¹' ((a.val \ b.val) ∪ (b.val \ a.val)) ∈ (F i).negligible
      intro i
      have hi := Quotient.exact (congrFun h i)
      change (Sigma.mk i ⁻¹' a.val \ Sigma.mk i ⁻¹' b.val) ∪
        (Sigma.mk i ⁻¹' b.val \ Sigma.mk i ⁻¹' a.val) ∈ (F i).negligible at hi
      simpa only [Set.preimage_union,Set.preimage_sdiff] using hi

theorem toFibres_le_iff (a b : MmodN (coprodEnhanced F)) :
    toFibres F a ≤ toFibres F b ↔ a ≤ b := by
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      change (∀ i, (Sigma.mk i ⁻¹' a.val \ Sigma.mk i ⁻¹' b.val) ∈ (F i).negligible) ↔
        ∀ i, Sigma.mk i ⁻¹' (a.val \ b.val) ∈ (F i).negligible
      simp only [Set.preimage_sdiff]

def coprodOrderIso : MmodN (coprodEnhanced F) ≃o ∀ i, MmodN (F i) where
  toEquiv := Equiv.ofBijective (toFibres F)
    ⟨toFibres_injective F, fun a => ⟨fromFibres F a,to_from F a⟩⟩
  map_rel_iff' := fun {a b} => toFibres_le_iff F a b

theorem partialPreimage_sdiff {X Z : Type u} (f : X → Option Z) (a b : Set Z) :
    partialPreimage f (a \ b) = partialPreimage f a \ partialPreimage f b := by
  ext x
  cases hfx : f x <;> simp [partialPreimage,hfx]

theorem pullPremap_mono {X Z : Type u} {E : Enhanced X} {G : Enhanced Z}
    (f : Premap E G) : Monotone (pullPremap f) := by
  intro a b
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      intro h
      change partialPreimage f.val a.val \ partialPreimage f.val b.val ∈ E.negligible
      rw [← partialPreimage_sdiff]
      exact f.property.2.2 _ h

theorem pull_inverse {X Z : Type u} {E : Enhanced X} {G : Enhanced Z}
    (f : Premap E G) (g : Premap G E)
    (hgf : partialCompose g.val f.val = fun x => some x) (a : MmodN E) :
    pullPremap f (pullPremap g a) = a := by
  induction a using Quotient.ind with
  | _ a =>
    apply Quotient.sound
    change (partialPreimage f.val (partialPreimage g.val a.val) \ a.val) ∪
      (a.val \ partialPreimage f.val (partialPreimage g.val a.val)) ∈ E.negligible
    rw [← partialPreimage_comp,hgf,partialPreimage_id]
    simpa using E.sigmaIdeal.1

def premapOrderIso {X Z : Type u} {E : Enhanced X} {G : Enhanced Z}
    (f : Premap E G) (g : Premap G E)
    (hgf : partialCompose g.val f.val = fun x => some x)
    (hfg : partialCompose f.val g.val = fun z => some z) : MmodN E ≃o MmodN G where
  toFun := pullPremap g
  invFun := pullPremap f
  left_inv := pull_inverse f g hgf
  right_inv := pull_inverse g f hfg
  map_rel_iff' := by
    intro a b
    change pullPremap g a ≤ pullPremap g b ↔ a ≤ b
    constructor
    · intro h
      simpa only [pull_inverse f g hgf] using pullPremap_mono f h
    · intro h
      exact pullPremap_mono g h

end Gelfand454Coprod
end
end Gelfand516Source30

/- Source: Work.Gelfand516.Main; SHA256 0d1748c02ead98afe27e31ad7991aed271cde70258ac0c09338a3b64ae9f4e80. -/
section Gelfand516Source31

set_option autoImplicit false
noncomputable section
open Set CategoryTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand516Final
universe u

/-- The Boolean presentation is the canonical product-of-components
construction already used in Proposition4.54. Its order remains the quotient order. -/
theorem exists_boolean_presentation {X : Type u} (E : Enhanced X)
    (hE : IsStrictlyLocalizable E) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B), Nonempty (MmodN E ≃o B) := by
  classical
  obtain ⟨I, Y, F, hF, f, g, hgf, hfg⟩ := hE
  letI (i : I) : CompleteBooleanAlgebra (MmodN (F i)) :=
    Gelfand454.quotientCompleteBooleanAlgebra (F i) (hF i)
  exact ⟨(∀ i, MmodN (F i)), inferInstance,
    ⟨(Gelfand454Coprod.premapOrderIso f g hgf hfg).trans (Gelfand454Coprod.coprodOrderIso F)⟩⟩

end Gelfand516Final

universe u

/-- Every canonical compact strictly localizable enhanced measurable space
is isomorphic in EMS to the Stone spectrum of its quotient Boolean algebra. -/
theorem solution (A : CSLEMS.{u}) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B), Nonempty (MmodN A.obj.E ≃o B) ∧
      Nonempty (A.obj ≅ EMS.of (stoneSpectrum B) (TM (stoneSpectrum B))) := by
  obtain ⟨B, hB, ⟨e⟩⟩ := Gelfand516Final.exists_boolean_presentation A.obj.E A.property.2
  letI : CompleteBooleanAlgebra B := hB
  refine ⟨B, hB, ⟨e⟩, ?_⟩
  exact Gelfand516Compact.ems_iso_of_lifting_on_nonnull A.obj.E e A.property.1 A.property.2
    (fun hn => Gelfand516Lifting.exists_booleanSection_of_strictlyLocalizable
      A.obj.E e A.property.2 hn)
end
end Gelfand516Source31
