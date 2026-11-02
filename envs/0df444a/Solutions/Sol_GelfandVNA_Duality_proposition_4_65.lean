-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_4_65
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T05:18:17.475707+00:00
-- url     : https://prove2.me/submissions/bcdeee99-cb7f-4dcd-a0d4-00e5d82628e1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_EMS

/-!
Direct proof of the current Proposition 4.65 of Pavlov, arXiv:2005.05284v3.
Canonical definitions are imported unchanged. All supporting proofs are included.
The compact null-family argument proves both the atomless and nonprincipal-atom branches.
-/
noncomputable section

section Gelfand465_part_Work_Gelfand465_Kernel
set_option autoImplicit false
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand465
universe u

def measurableSpace {X : Type u} (E : Enhanced X) : MeasurableSpace X :=
  ⟨E.measurable, E.sigmaAlgebra.1, E.sigmaAlgebra.2.1, E.sigmaAlgebra.2.2⟩

private theorem measurable_diff {X : Type u} (E : Enhanced X) {a b : Set X}
    (ha : a ∈ E.measurable) (hb : b ∈ E.measurable) : a \ b ∈ E.measurable := by
  letI := measurableSpace E
  have hma : MeasurableSet a := ha
  have hmb : MeasurableSet b := hb
  exact hma.diff hmb

theorem partialPreimage_mono {X Y : Type u} (f : X → Option Y) {a b : Set Y}
    (hab : a ⊆ b) : partialPreimage f a ⊆ partialPreimage f b := by
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, hab hy, hxy⟩

/-- The uniqueness half of Proposition 4.65 needs no compactness or measures. -/
theorem measurableImage_unique {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f : Premap E F) {m₀ m₁ : Set Y}
    (h₀ : IsMeasurableImage E F f m₀) (h₁ : IsMeasurableImage E F f m₁) :
    (m₀ \ m₁) ∪ (m₁ \ m₀) ∈ F.negligible := by
  apply negligible_union F
  · apply h₀.2.2 (m₀ \ m₁) (measurable_diff F h₀.1 h₁.1) sdiff_subset
    exact negligible_mono E (partialPreimage_mono f.1 (fun _ hx => hx.2)) h₁.2.1
  · apply h₁.2.2 (m₁ \ m₀) (measurable_diff F h₁.1 h₀.1) sdiff_subset
    exact negligible_mono E (partialPreimage_mono f.1 (fun _ hx => hx.2)) h₀.2.1

/-- A measurable image is precisely the complement of a greatest measurable
set with negligible inverse image, where greatness is modulo negligible sets. -/
theorem measurableImage_compl_iff {X Y : Type u} (E : Enhanced X) (F : Enhanced Y)
    (f : Premap E F) (p : Set Y) :
    IsMeasurableImage E F f pᶜ ↔
      p ∈ F.measurable ∧ partialPreimage f.1 p ∈ E.negligible ∧
        ∀ a ∈ F.measurable, partialPreimage f.1 a ∈ E.negligible →
          a \ p ∈ F.negligible := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [compl_compl] using F.sigmaAlgebra.2.1 pᶜ h.1
    · simpa only [compl_compl] using h.2.1
    · intro a ha hfa
      apply h.2.2 (a \ p) (measurable_diff F ha ?_) (fun _ hx => hx.2)
      · exact negligible_mono E (partialPreimage_mono f.1 sdiff_subset) hfa
      · simpa only [compl_compl] using F.sigmaAlgebra.2.1 pᶜ h.1
  · rintro ⟨hp, hfp, hmax⟩
    refine ⟨F.sigmaAlgebra.2.1 p hp, ?_, ?_⟩
    · simpa only [compl_compl] using hfp
    · intro a ha hap hfa
      have h := hmax a ha hfa
      have he : a \ p = a := by
        ext y
        exact ⟨fun hy => hy.1, fun hy => ⟨hy, hap hy⟩⟩
      rwa [he] at h

theorem mk_eq_empty_iff {X : Type u} (E : Enhanced X) (a : Set X)
    (ha : a ∈ E.measurable) :
    MmodN.mk a ha = MmodN.mk ∅ E.sigmaAlgebra.1 ↔ a ∈ E.negligible := by
  change Quotient.mk (nullSetoid E) ⟨a, ha⟩ =
    Quotient.mk (nullSetoid E) ⟨∅, E.sigmaAlgebra.1⟩ ↔ _
  rw [Quotient.eq]
  change (a \ ∅) ∪ (∅ \ a) ∈ E.negligible ↔ _
  simp only [sdiff_empty, empty_sdiff, union_empty]

/-- The kernel here uses only the canonical quotient and canonical pullback;
no new lattice structure on the quotient is needed. -/
def pullbackKernel {X Y : Type u} {E : Enhanced X} {F : Enhanced Y}
    (f : Premap E F) : Set (MmodN F) :=
  {q | pullPremap f q = MmodN.mk ∅ E.sigmaAlgebra.1}

theorem measurableImage_iff_greatest_kernel {X Y : Type u}
    (E : Enhanced X) (F : Enhanced Y) (f : Premap E F) (p : Set Y)
    (hp : p ∈ F.measurable) :
    IsMeasurableImage E F f pᶜ ↔ IsGreatest (pullbackKernel f) (MmodN.mk p hp) := by
  rw [measurableImage_compl_iff]
  constructor
  · rintro ⟨_, hfp, hmax⟩
    refine ⟨?_, ?_⟩
    · exact (mk_eq_empty_iff E _ (f.2.2.1 p hp)).mpr hfp
    · intro q hq
      induction q using Quotient.inductionOn with
      | h a =>
        change a.val \ p ∈ F.negligible
        apply hmax a.val a.property
        exact (mk_eq_empty_iff E _ (f.2.2.1 a.val a.property)).mp hq
  · rintro ⟨hfp, hmax⟩
    refine ⟨hp, (mk_eq_empty_iff E _ (f.2.2.1 p hp)).mp hfp, ?_⟩
    intro a ha hfa
    exact hmax (show MmodN.mk a ha ∈ pullbackKernel f from
      (mk_eq_empty_iff E _ (f.2.2.1 a ha)).mpr hfa)

/-- Existence in Proposition 4.65 is exactly the assertion that the pullback
kernel has a greatest element. The hypothesis is an internal proof obligation,
not an extra assumption on the frozen proposition. -/
theorem exists_measurableImage_iff {X Y : Type u}
    (E : Enhanced X) (F : Enhanced Y) (f : Premap E F) :
    (∃ m, IsMeasurableImage E F f m) ↔ ∃ q, IsGreatest (pullbackKernel f) q := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨MmodN.mk mᶜ (F.sigmaAlgebra.2.1 m hm.1), ?_⟩
    apply (measurableImage_iff_greatest_kernel E F f mᶜ _).mp
    simpa only [compl_compl] using hm
  · rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn with
    | h a =>
      exact ⟨a.valᶜ, (measurableImage_iff_greatest_kernel E F f a.val a.property).mpr hq⟩

/-- The countable kernel-supremum step used on each sigma-finite component in
the source proof of Proposition 4.65. -/
theorem exists_measurableImage_of_countable_kernel {X Y : Type u}
    (E : Enhanced X) (F : Enhanced Y) (f : Premap E F)
    (r : ℕ → Set Y) (hr : ∀ n, r n ∈ F.measurable)
    (hfr : ∀ n, partialPreimage f.1 (r n) ∈ E.negligible)
    (hcofinal : ∀ a ∈ F.measurable, partialPreimage f.1 a ∈ E.negligible →
      a \ (⋃ n, r n) ∈ F.negligible) :
    ∃ m, IsMeasurableImage E F f m := by
  refine ⟨(⋃ n, r n)ᶜ, (measurableImage_compl_iff E F f _).mpr ?_⟩
  refine ⟨F.sigmaAlgebra.2.2 r hr, ?_, ?_⟩
  · have he : partialPreimage f.1 (⋃ n, r n) = ⋃ n, partialPreimage f.1 (r n) := by
      ext x
      simp only [partialPreimage, mem_iUnion, mem_setOf_eq]
      constructor
      · rintro ⟨y, ⟨n, hy⟩, hxy⟩
        exact ⟨n, y, hy, hxy⟩
      · rintro ⟨n, y, hy, hxy⟩
        exact ⟨y, ⟨n, hy⟩, hxy⟩
    rw [he]
    exact E.sigmaIdeal.2.2 _ hfr
  · intro a ha hfa
    exact hcofinal a ha hfa

end Gelfand465
end Gelfand465_part_Work_Gelfand465_Kernel

section Gelfand465_part_Work_Gelfand465_FiniteKernel
set_option autoImplicit false
open Set Filter MeasureTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20
open scoped ENNReal Topology

namespace Gelfand465
universe u

/-- In a finite measure space, a collection closed under countable unions has
a member containing every other member modulo measure zero. -/
theorem countableUnionClosed_has_maximum {Y : Type u} [MeasurableSpace Y]
    (ν : Measure Y) [IsFiniteMeasure ν] (S : Set (Set Y))
    (hempty : ∅ ∈ S) (hM : ∀ a ∈ S, MeasurableSet a)
    (hU : ∀ r : ℕ → Set Y, (∀ n, r n ∈ S) → (⋃ n, r n) ∈ S) :
    ∃ p ∈ S, ∀ a ∈ S, ν (a \ p) = 0 := by
  classical
  obtain ⟨v, _, _, hv, hvmem⟩ :=
    (isLUB_sSup (ν '' S)).exists_seq_monotone_tendsto
      ⟨ν ∅, ∅, hempty, rfl⟩
  choose r hr hrv using hvmem
  let p : Set Y := ⋃ n, r n
  have hp : p ∈ S := hU r hr
  have hsup : sSup (ν '' S) ≤ ν p := by
    apply le_of_tendsto hv
    apply Filter.Eventually.of_forall
    intro n
    rw [← hrv n]
    exact measure_mono (subset_iUnion r n)
  have hpmax : ∀ a ∈ S, ν a ≤ ν p := by
    intro a ha
    exact (le_sSup (mem_image_of_mem ν ha)).trans hsup
  refine ⟨p, hp, ?_⟩
  intro a ha
  have hu : a ∪ p ∈ S := by
    have h := hU (fun n => if n = 0 then a else p) (by
      intro n
      split_ifs <;> assumption)
    rwa [iUnion_two] at h
  rw [measure_sdiff' a (hM p hp).nullMeasurableSet (measure_ne_top ν p)]
  exact tsub_eq_zero_of_le (hpmax (a ∪ p) hu)

/-- The sigma-finite-codomain part of Proposition 4.65, expressed using a
faithful finite positive measure. No compactness of the source is required. -/
theorem exists_measurableImage_of_finiteMeasure {X Y : Type u}
    (E : Enhanced X) (F : Enhanced Y) (f : Premap E F)
    (ν : @Measure Y (measurableSpace F))
    [@IsFiniteMeasure Y (measurableSpace F) ν]
    (hnull : ∀ a : Set Y, ν a = 0 ↔ a ∈ F.negligible) :
    ∃ m, IsMeasurableImage E F f m := by
  letI := measurableSpace F
  let S : Set (Set Y) := {a | a ∈ F.measurable ∧ partialPreimage f.1 a ∈ E.negligible}
  have hempty : ∅ ∈ S := by
    refine ⟨F.sigmaAlgebra.1, ?_⟩
    have he : partialPreimage f.1 ∅ = ∅ := by ext x; simp [partialPreimage]
    rw [he]
    exact E.sigmaIdeal.1
  have hU : ∀ r : ℕ → Set Y, (∀ n, r n ∈ S) → (⋃ n, r n) ∈ S := by
    intro r hr
    refine ⟨F.sigmaAlgebra.2.2 r (fun n => (hr n).1), ?_⟩
    have he : partialPreimage f.1 (⋃ n, r n) = ⋃ n, partialPreimage f.1 (r n) := by
      ext x
      simp only [partialPreimage, mem_iUnion, mem_setOf_eq]
      constructor
      · rintro ⟨y, ⟨n, hy⟩, hxy⟩
        exact ⟨n, y, hy, hxy⟩
      · rintro ⟨n, y, hy, hxy⟩
        exact ⟨y, ⟨n, hy⟩, hxy⟩
    rw [he]
    exact E.sigmaIdeal.2.2 _ (fun n => (hr n).2)
  obtain ⟨p, hp, hmax⟩ := countableUnionClosed_has_maximum ν S hempty (fun _ ha => ha.1) hU
  refine ⟨pᶜ, (measurableImage_compl_iff E F f p).mpr ⟨hp.1, hp.2, ?_⟩⟩
  intro a ha hfa
  exact (hnull (a \ p)).mp (hmax a ⟨ha, hfa⟩)

end Gelfand465
end Gelfand465_part_Work_Gelfand465_FiniteKernel

section Gelfand465_part_Work_Gelfand454_FiniteMeasure
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
end Gelfand465_part_Work_Gelfand454_FiniteMeasure

section Gelfand465_part_Work_Gelfand465_CoproductKernel
open Set MeasureTheory GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand465Assembly
universe u v

lemma partialPreimage_iUnion {X Y : Type u} {I : Type v} (f : X → Option Y) (r : I → Set Y) :
    partialPreimage f (⋃ i, r i) = ⋃ i, partialPreimage f (r i) := by
  ext x
  simp only [partialPreimage, mem_iUnion, mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨i, hy⟩, hfx⟩
    exact ⟨i, y, hy, hfx⟩
  · rintro ⟨i, y, hy, hfx⟩
    exact ⟨y, ⟨i, hy⟩, hfx⟩

/-- Component kernel maxima require only countable-union closure. We do not
pretend that the component restriction of a premap has conull domain. -/
theorem exists_kernelMaximum_coprod {X I : Type u} {Y : I → Type u}
    (E : Enhanced X) (F : ∀ i, Enhanced (Y i)) (hF : ∀ i, IsSigmaFiniteE (F i))
    (f : Premap E (coprodEnhanced F))
    (hunion : ∀ r : I → Set X, Pairwise (Function.onFun Disjoint r) →
      (∀ J : Set I, (⋃ i ∈ J, r i) ∈ E.measurable) →
      (∀ i, r i ∈ E.negligible) → (⋃ i, r i) ∈ E.negligible) :
    ∃ p : Set (Σ i, Y i), p ∈ (coprodEnhanced F).measurable ∧
      partialPreimage f.val p ∈ E.negligible ∧
      ∀ a ∈ (coprodEnhanced F).measurable, partialPreimage f.val a ∈ E.negligible →
        a \ p ∈ (coprodEnhanced F).negligible := by
  classical
  have hcomponent (i : I) : ∃ p : Set (Y i), p ∈ (F i).measurable ∧
      partialPreimage f.val (Sigma.mk i '' p) ∈ E.negligible ∧
      ∀ a ∈ (F i).measurable, partialPreimage f.val (Sigma.mk i '' a) ∈ E.negligible →
        a \ p ∈ (F i).negligible := by
    letI := Gelfand454.measurableSpace (F i)
    obtain ⟨ν, hν, hnull⟩ := Gelfand454.exists_finiteMeasure (F i) (hF i)
    letI := hν
    let C : Set (Set (Y i)) := {a | a ∈ (F i).measurable ∧
      partialPreimage f.val (Sigma.mk i '' a) ∈ E.negligible}
    have hCempty : ∅ ∈ C := by
      refine ⟨(F i).sigmaAlgebra.1, ?_⟩
      have he : partialPreimage f.val (Sigma.mk i '' (∅ : Set (Y i))) = ∅ := by
        ext x
        simp [partialPreimage]
      rw [he]
      exact E.sigmaIdeal.1
    have hCU (r : ℕ → Set (Y i)) (hr : ∀ n, r n ∈ C) : (⋃ n, r n) ∈ C := by
      refine ⟨(F i).sigmaAlgebra.2.2 r (fun n => (hr n).1), ?_⟩
      rw [image_iUnion, partialPreimage_iUnion]
      exact E.sigmaIdeal.2.2 _ (fun n => (hr n).2)
    obtain ⟨p, hp, hmax⟩ := Gelfand465.countableUnionClosed_has_maximum ν C hCempty
      (fun a ha => ha.1) hCU
    exact ⟨p, hp.1, hp.2, fun a ha hfa => (hnull (a \ p)).mp (hmax a ⟨ha, hfa⟩)⟩
  choose p hp hpn hmax using hcomponent
  let P : Set (Σ i, Y i) := {y | y.2 ∈ p y.1}
  have hPm : P ∈ (coprodEnhanced F).measurable := fun i => hp i
  let r : I → Set X := fun i => partialPreimage f.val (Sigma.mk i '' p i)
  have hrdis : Pairwise (Function.onFun Disjoint r) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨y, ⟨a, ha, rfl⟩, hfx⟩ ⟨z, ⟨b, hb, rfl⟩, hfx'⟩
    exact hij (congrArg Sigma.fst (Option.some.inj (hfx.symm.trans hfx')))
  have hrsub (J : Set I) : (⋃ i ∈ J, r i) ∈ E.measurable := by
    let Q : Set (Σ i, Y i) := {y | y.1 ∈ J ∧ y.2 ∈ p y.1}
    have hQm : Q ∈ (coprodEnhanced F).measurable := by
      intro i
      by_cases hi : i ∈ J
      · have he : Sigma.mk i ⁻¹' Q = p i := by ext y; simp [Q, hi]
        rw [he]
        exact hp i
      · have he : Sigma.mk i ⁻¹' Q = ∅ := by ext y; simp [Q, hi]
        rw [he]
        exact (F i).sigmaAlgebra.1
    have he : (⋃ i ∈ J, r i) = partialPreimage f.val Q := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i, hi, y, ⟨a, ha, rfl⟩, hfx⟩
        exact ⟨⟨i, a⟩, ⟨hi, ha⟩, hfx⟩
      · rintro ⟨⟨i, a⟩, ⟨hi, ha⟩, hfx⟩
        exact ⟨i, hi, ⟨i, a⟩, ⟨a, ha, rfl⟩, hfx⟩
    rw [he]
    exact f.property.2.1 Q hQm
  have hrn : (⋃ i, r i) ∈ E.negligible := hunion r hrdis hrsub hpn
  have hPr : partialPreimage f.val P = ⋃ i, r i := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨⟨i, a⟩, ha, hfx⟩
      exact ⟨i, ⟨i, a⟩, ⟨a, ha, rfl⟩, hfx⟩
    · rintro ⟨i, y, ⟨a, ha, rfl⟩, hfx⟩
      exact ⟨⟨i, a⟩, ha, hfx⟩
  refine ⟨P, hPm, hPr.symm ▸ hrn, ?_⟩
  intro a ha hfa i
  change ((Sigma.mk i ⁻¹' a) \ p i) ∈ (F i).negligible
  apply hmax i (Sigma.mk i ⁻¹' a) (ha i)
  apply negligible_mono E (Gelfand465.partialPreimage_mono f.val ?_) hfa
  exact image_preimage_subset (Sigma.mk i) a

end Gelfand465Assembly
end Gelfand465_part_Work_Gelfand465_CoproductKernel

section Gelfand465_part_Work_Gelfand465_KernelTransport
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand465Assembly
universe u

lemma partialPreimage_sdiff {X Y : Type u} (f : X → Option Y) (a b : Set Y) :
    partialPreimage f (a \ b) = partialPreimage f a \ partialPreimage f b := by
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyn⟩, hfy⟩
    refine ⟨⟨y, hy, hfy⟩, ?_⟩
    rintro ⟨z, hz, hfz⟩
    have he : y = z := Option.some.inj (hfy.symm.trans hfz)
    exact hyn (he.symm ▸ hz)
  · rintro ⟨⟨y, hy, hfy⟩, hn⟩
    exact ⟨y, ⟨hy, fun hb => hn ⟨y, hb, hfy⟩⟩, hfy⟩

/-- Pull a greatest kernel set back across actual inverse premaps. The only
identity needed is the literal left inverse on the original codomain. -/
theorem kernelMaximum_transport {X Y Z : Type u}
    (E : Enhanced X) (F : Enhanced Y) (G : Enhanced Z) (f : Premap E F)
    (a : Premap F G) (b : Premap G F)
    (hleft : partialCompose b.val a.val = fun y => some y)
    (p : Set Z) (hpm : p ∈ G.measurable)
    (hpn : partialPreimage (compPremap f a).val p ∈ E.negligible)
    (hmax : ∀ s ∈ G.measurable, partialPreimage (compPremap f a).val s ∈ E.negligible →
      s \ p ∈ G.negligible) :
    partialPreimage a.val p ∈ F.measurable ∧
      partialPreimage f.val (partialPreimage a.val p) ∈ E.negligible ∧
      ∀ s ∈ F.measurable, partialPreimage f.val s ∈ E.negligible →
        s \ partialPreimage a.val p ∈ F.negligible := by
  refine ⟨a.property.2.1 p hpm, ?_, ?_⟩
  · simpa only [compPremap, partialPreimage_comp] using hpn
  · intro s hs hfs
    have he : partialPreimage a.val (partialPreimage b.val s) = s := by
      rw [← partialPreimage_comp, hleft, partialPreimage_id]
    have hbs : partialPreimage (compPremap f a).val (partialPreimage b.val s) ∈ E.negligible := by
      change partialPreimage (partialCompose a.val f.val) (partialPreimage b.val s) ∈ E.negligible
      rw [partialPreimage_comp, he]
      exact hfs
    have hn := a.property.2.2 _ (hmax _ (b.property.2.1 s hs) hbs)
    rwa [partialPreimage_sdiff, he] at hn

end Gelfand465Assembly
end Gelfand465_part_Work_Gelfand465_KernelTransport

section Gelfand465_part_Work_Gelfand465_Perfect_CompactTopology
open Set TopologicalSpace QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand465Perfect
universe u
variable {X : Type u}

/-- Fremlin342D: the complements of a compact class generate a compact topology. -/
@[instance_reducible] def compactClassTopology (K : Set (Set X)) : TopologicalSpace X :=
  TopologicalSpace.generateFrom (compl '' K)

theorem compactClassTopology_isClosed (K : Set (Set X)) {k : Set X} (hk : k ∈ K) :
    @IsClosed X (compactClassTopology K) k := by
  letI := compactClassTopology K
  apply isOpen_compl_iff.mp
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, hk, rfl⟩

theorem compactClassTopology_compact (K : Set (Set X))
    (hK : IsCompactClassOn (univ : Set X) K) :
    @CompactSpace X (compactClassTopology K) := by
  letI := compactClassTopology K
  apply compactSpace_generateFrom rfl
  intro P hPK hP
  contrapose! hP
  simp_rw [← Set.nonempty_compl, Set.compl_sUnion] at hP ⊢
  have hsub : compl '' P ⊆ K := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hPK ht
    simpa only [compl_compl] using hk
  obtain ⟨x, _, hx⟩ := hK (compl '' P) hsub (by
    intro Q hQ hQP
    have h : (⋂₀ Q).Nonempty := by
      have h' : Q ⊆ compl '' P → (compl '' Q).Finite → (⋂₀ Q).Nonempty := by
        simpa [← compl_involutive.image_eq_preimage_symm] using hP (compl '' Q)
      exact h' hQP (hQ.image _)
    simpa only [univ_inter] using h)
  exact ⟨x, hx⟩

/-- The canonical compact-class predicate gives the compact topology from
Fremlin342D without separation or measurability assumptions on that topology. -/
theorem exists_compactTopology (K : Set (Set X))
    (hK : IsCompactClassOn (univ : Set X) K) :
    ∃ t : TopologicalSpace X, @CompactSpace X t ∧ ∀ k ∈ K, @IsClosed X t k :=
  ⟨compactClassTopology K, compactClassTopology_compact K hK,
    fun _ hk => compactClassTopology_isClosed K hk⟩

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_CompactTopology

section Gelfand465_part_Work_Gelfand465_Perfect_InnerRegular
open Set MeasureTheory

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- The finite-measure case of Fremlin342B: an inner-positive class has a
countable subfamily covering each measurable set modulo a null set. -/
theorem exists_countable_inner_cover (K : Set (Set X))
    (hK : ∀ k ∈ K, MeasurableSet k)
    (hpos : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ k ∈ K, k ⊆ s ∧ μ k ≠ 0)
    {s : Set X} (hs : MeasurableSet s) :
    ∃ D : Set (Set X), D.Countable ∧ D ⊆ K ∧
      (∀ k ∈ D, k ⊆ s) ∧ μ (s \ ⋃₀ D) = 0 := by
  let C : Set (Set X) := {k | k ∈ K ∧ k ⊆ s}
  obtain ⟨D, hDC, hDc, hD⟩ := μ.exists_ae_subset_biUnion_countable
    (C := C) (fun k hk => hK k hk.1)
  refine ⟨D, hDc, fun k hk => (hDC hk).1, fun k hk => (hDC hk).2, ?_⟩
  by_contra hne
  have hDm : MeasurableSet (⋃₀ D) :=
    MeasurableSet.sUnion hDc (fun k hk => hK k (hDC hk).1)
  obtain ⟨k, hkK, hks, hk⟩ := hpos (s \ ⋃₀ D) (hs.diff hDm) hne
  have hnull := ae_le_set.1 (hD k ⟨hkK, hks.trans sdiff_subset⟩)
  have heq : k \ ⋃₀ D = k := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (hks hx).2⟩⟩
  exact hk (heq ▸ hnull)

/-- Fremlin342B/342C, finite-measure form: finite unions of an inner-positive
measurable class approximate every measurable set from within. -/
theorem innerRegular_finite_unions (K : Set (Set X))
    (hK : ∀ k ∈ K, MeasurableSet k)
    (hpos : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ k ∈ K, k ⊆ s ∧ μ k ≠ 0) :
    μ.InnerRegularWRT
      (fun t => ∃ D : Set (Set X), D.Finite ∧ D ⊆ K ∧ t = ⋃₀ D) MeasurableSet := by
  classical
  intro s hs a ha
  obtain ⟨D, hDc, hDK, hDs, hnull⟩ := exists_countable_inner_cover μ K hK hpos hs
  have hUs : ⋃₀ D ⊆ s := sUnion_subset hDs
  have hmeasure : μ (⋃₀ D) = μ s := by
    apply measure_congr
    exact ae_eq_set.2 ⟨by rw [sdiff_eq_empty.mpr hUs, measure_empty], hnull⟩
  have hDne : D.Nonempty := by
    by_contra hn
    have hDempty : D = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [hDempty, sUnion_empty, measure_empty] at hmeasure
    exact (not_lt_of_ge bot_le) (hmeasure.symm ▸ ha)
  obtain ⟨r, hr⟩ := hDc.exists_eq_range hDne
  have hsup : μ s = ⨆ n, μ (accumulate r n) := by
    rw [← hmeasure, hr, sUnion_range, measure_iUnion_eq_iSup_accumulate]
  obtain ⟨n, hn'⟩ := lt_iSup_iff.mp (hsup ▸ ha)
  refine ⟨accumulate r n, ?_, ⟨r '' Iic n, (finite_Iic n).image r, ?_, ?_⟩, hn'⟩
  · intro x hx
    obtain ⟨i, _, hi⟩ := mem_accumulate.mp hx
    exact hDs (r i) (hr.symm ▸ mem_range_self i) hi
  · rintro k ⟨i, hi, rfl⟩
    exact hDK (hr.symm ▸ mem_range_self i)
  · simp only [sUnion_image, mem_Iic, accumulate_def]

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_InnerRegular

section Gelfand465_part_Work_Gelfand465_Perfect_EnhancedCompact
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand465Perfect
universe u
variable {X : Type u}

/-- The canonical compact-enhanced predicate, together with a faithful finite
positive measure, gives inner regularity by measurable closed sets for a compact
topology. The topology is not asserted to be Hausdorff or Borel-compatible.
This is the finite-measure content of Fremlin342D--342F, not perfectness or451Q. -/
theorem compactEnhanced_innerRegular (E : Enhanced X)
    (hc : IsCompactEnhancedOn E univ)
    (μ : @Measure X (Gelfand454.measurableSpace E)) [IsFiniteMeasure μ]
    (hnull : ∀ s : Set X, μ s = 0 ↔ s ∈ E.negligible) :
    ∃ t : TopologicalSpace X, @CompactSpace X t ∧
      μ.InnerRegularWRT (fun k => @IsClosed X t k ∧ k ∈ E.measurable)
        (fun s => s ∈ E.measurable) := by
  letI := Gelfand454.measurableSpace E
  obtain ⟨K, hKm, hKc, hKi⟩ := hc
  have hK : ∀ k ∈ K, MeasurableSet k := fun k hk => (hKm k hk).2
  have hpos : ∀ s, MeasurableSet s → μ s ≠ 0 →
      ∃ k ∈ K, k ⊆ s ∧ μ k ≠ 0 := by
    intro s hs hμs
    obtain ⟨k, hk, hks, hkn⟩ := hKi s (subset_univ _) hs
      (fun hn => hμs ((hnull s).2 hn))
    exact ⟨k, hk, hks, fun hzero => hkn ((hnull k).1 hzero)⟩
  letI := compactClassTopology K
  refine ⟨compactClassTopology K, compactClassTopology_compact K hKc, ?_⟩
  intro s hs a ha
  obtain ⟨k, hks, ⟨D, hDf, hDK, rfl⟩, hak⟩ :=
    innerRegular_finite_unions μ K hK hpos hs a ha
  refine ⟨⋃₀ D, hks, ⟨?_, ?_⟩, hak⟩
  · rw [sUnion_eq_biUnion]
    exact hDf.isClosed_biUnion (fun k hk => compactClassTopology_isClosed K (hDK hk))
  · exact MeasurableSet.sUnion hDf.countable (fun k hk => hK k (hDK hk))

/-- The finite-enhanced-measure hypothesis is canonical `IsSigmaFiniteE`;
the finite positive measure and its exact null ideal are constructed, not assumed. -/
theorem sigmaFinite_compactEnhanced_innerRegular (E : Enhanced X)
    (hc : IsCompactEnhancedOn E univ) (hE : IsSigmaFiniteE E) :
    ∃ (μ : @Measure X (Gelfand454.measurableSpace E)) (t : TopologicalSpace X),
      IsFiniteMeasure μ ∧ (∀ s : Set X, μ s = 0 ↔ s ∈ E.negligible) ∧
      @CompactSpace X t ∧
      μ.InnerRegularWRT (fun k => @IsClosed X t k ∧ k ∈ E.measurable)
        (fun s => s ∈ E.measurable) := by
  obtain ⟨μ, hμ, hnull⟩ := Gelfand454.exists_finiteMeasure E hE
  letI := hμ
  obtain ⟨t, ht, hreg⟩ := compactEnhanced_innerRegular E hc μ hnull
  exact ⟨μ, t, hμ, hnull, ht, hreg⟩

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_EnhancedCompact

section Gelfand465_part_Work_Gelfand465_Perfect_RelativeCompact
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand465Perfect
universe u
variable {X : Type u}

/-- The original compact class remains inner positive for a finite measure
whose null sets are detected after intersection with one measurable carrier.
The topology stays on the actual whole source space. -/
theorem compactEnhanced_innerRegular_relative (E : Enhanced X)
    (hc : IsCompactEnhancedOn E univ) (m : Set X) (hm : m ∈ E.measurable)
    (μ : @Measure X (Gelfand454.measurableSpace E)) [IsFiniteMeasure μ]
    (hnull : ∀ s : Set X, s ∈ E.measurable → (μ s = 0 ↔ s ∩ m ∈ E.negligible)) :
    ∃ t : TopologicalSpace X, @CompactSpace X t ∧
      μ.InnerRegularWRT (fun k => @IsClosed X t k ∧ k ∈ E.measurable)
        (fun s => s ∈ E.measurable) := by
  letI := Gelfand454.measurableSpace E
  obtain ⟨K, hKm, hKc, hKi⟩ := hc
  have hK : ∀ k ∈ K, MeasurableSet k := fun k hk => (hKm k hk).2
  have hpos : ∀ s, MeasurableSet s → μ s ≠ 0 →
      ∃ k ∈ K, k ⊆ s ∧ μ k ≠ 0 := by
    intro s hs hμs
    have hm' : MeasurableSet m := hm
    have hsm : s ∩ m ∈ E.measurable := hs.inter hm'
    obtain ⟨k, hk, hks, hkn⟩ := hKi (s ∩ m) (subset_univ _) hsm
      (fun hn => hμs ((hnull s hs).2 hn))
    refine ⟨k, hk, hks.trans inter_subset_left, ?_⟩
    intro hz
    have hn := (hnull k (hK k hk)).1 hz
    rw [inter_eq_left.mpr (hks.trans inter_subset_right)] at hn
    exact hkn hn
  letI := compactClassTopology K
  refine ⟨compactClassTopology K, compactClassTopology_compact K hKc, ?_⟩
  intro s hs a ha
  obtain ⟨k, hks, ⟨D, hDf, hDK, rfl⟩, hak⟩ :=
    innerRegular_finite_unions μ K hK hpos hs a ha
  refine ⟨⋃₀ D, hks, ⟨?_, ?_⟩, hak⟩
  · rw [sUnion_eq_biUnion]
    exact hDf.isClosed_biUnion (fun k hk => compactClassTopology_isClosed K (hDK hk))
  · exact MeasurableSet.sUnion hDf.countable (fun k hk => hK k (hDK hk))

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_RelativeCompact

section Gelfand465_part_Work_Gelfand465_Perfect_FiniteComplexRestriction
set_option autoImplicit false
open Set MeasureTheory GelfandVNA.Duality
open QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand465Perfect
universe u
variable {X : Type u} (E : Enhanced X) (M' : Set (Set X)) (μ : Set X → ℂ)

theorem inter_mem_emMeasure (hμ : IsEMeasure E M' μ) (m : Set X) (hm : m ∈ M')
    {s : Set X} (hs : s ∈ E.measurable) : s ∩ m ∈ M' := by
  letI := Gelfand454.measurableSpace E
  have hsm : MeasurableSet s := hs
  have hmm : MeasurableSet m := hμ.1 hm
  exact hμ.2.2.2.1 m hm (s ∩ m) (hsm.inter hmm) inter_subset_right

/-- Restricting an enhanced complex measure to one element of its finite ideal
gives a finite enhanced measure on the unchanged ambient space. -/
theorem isEMeasure_inter (hμ : IsEMeasure E M' μ) (m : Set X) (hm : m ∈ M') :
    IsEMeasure E E.measurable (fun s => μ (s ∩ m)) := by
  letI := Gelfand454.measurableSpace E
  have hadd (f : ℕ → Set X) (hf : ∀ i, f i ∈ E.measurable)
      (hd : Pairwise (Function.onFun Disjoint f)) :
      Summable (fun i => ‖μ (f i ∩ m)‖) ∧
        HasSum (fun i => μ (f i ∩ m)) (μ ((⋃ i, f i) ∩ m)) := by
    have hmem (i : ℕ) : f i ∩ m ∈ M' := inter_mem_emMeasure E M' μ hμ m hm (hf i)
    have hdis : Pairwise (Function.onFun Disjoint (fun i => f i ∩ m)) := by
      intro i j hij
      exact (hd hij).mono inter_subset_left inter_subset_left
    have hunion : (⋃ i, f i ∩ m) ∈ M' := by
      rw [← iUnion_inter]
      exact inter_mem_emMeasure E M' μ hμ m hm (E.sigmaAlgebra.2.2 f hf)
    simpa only [iUnion_inter] using hμ.2.2.2.2.2.1 (fun i => f i ∩ m) hmem hdis hunion
  refine ⟨fun _ h => h, E.negligibleMeasurable, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    exact (show MeasurableSet a from ha).union (show MeasurableSet b from hb)
  · intro a ha b hb _
    exact hb
  · intro n hn
    exact hμ.2.2.2.2.1 _ (negligible_mono E inter_subset_left hn)
  · intro f hf hd _
    exact hadd f hf hd
  · intro f hf hd _
    exact ⟨E.sigmaAlgebra.2.2 f hf, (hadd f hf hd).2⟩

/-- The positive measure of a finite complex restriction detects precisely the
original negligible sets inside that restriction, without global faithfulness
of the restricted measure. -/
theorem finiteMeasure_inter_null_iff_measurable (hμ : IsEMeasure E M' μ)
    (hf : IsFaithfulEMeasure E M' μ) (m : Set X) (hm : m ∈ M')
    {s : Set X} (hs : s ∈ E.measurable) :
    Gelfand454.finiteMeasure E (fun t => μ (t ∩ m)) (isEMeasure_inter E M' μ hμ m hm) s = 0 ↔
      s ∩ m ∈ E.negligible := by
  letI := Gelfand454.measurableSpace E
  let μm : Set X → ℂ := fun t => μ (t ∩ m)
  let hμm : IsEMeasure E E.measurable μm := isEMeasure_inter E M' μ hμ m hm
  change Gelfand454.finiteMeasure E μm hμm s = 0 ↔ s ∩ m ∈ E.negligible
  have hsm : MeasurableSet s := hs
  rw [Gelfand454.finiteMeasure, Measure.add_apply, add_eq_zero,
    SignedMeasure.totalVariation_eq_variation,
    SignedMeasure.totalVariation_eq_variation,
    VectorMeasure.variation_apply_eq_zero hsm,
    VectorMeasure.variation_apply_eq_zero hsm]
  constructor
  · rintro ⟨hr, hi⟩
    apply hf (s ∩ m) (inter_mem_emMeasure E M' μ hμ m hm hs)
    intro t ht hts
    have htm : t ⊆ m := hts.trans inter_subset_right
    have htmeas : t ∈ E.measurable := hμ.1 ht
    apply Complex.ext
    · have h := hr t (hts.trans inter_subset_left) htmeas
      change (Gelfand454.complexMeasureOf E μm hμm t).re = 0 at h
      rw [Gelfand454.complexMeasureOf_apply E μm hμm htmeas] at h
      simpa only [μm, inter_eq_left.mpr htm, Complex.zero_re] using h
    · have h := hi t (hts.trans inter_subset_left) htmeas
      change (Gelfand454.complexMeasureOf E μm hμm t).im = 0 at h
      rw [Gelfand454.complexMeasureOf_apply E μm hμm htmeas] at h
      simpa only [μm, inter_eq_left.mpr htm, Complex.zero_im] using h
  · intro hn
    have hzero : ∀ t, t ⊆ s → t ∈ E.measurable →
        Gelfand454.complexMeasureOf E μm hμm t = 0 := by
      intro t hts ht
      rw [Gelfand454.complexMeasureOf_apply E μm hμm ht]
      exact hμ.2.2.2.2.1 _ (negligible_mono E (inter_subset_inter hts (Subset.rfl : m ⊆ m)) hn)
    constructor
    · intro t hts ht
      change (Gelfand454.complexMeasureOf E μm hμm t).re = 0
      rw [hzero t hts ht, Complex.zero_re]
    · intro t hts ht
      change (Gelfand454.complexMeasureOf E μm hμm t).im = 0
      rw [hzero t hts ht, Complex.zero_im]

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_FiniteComplexRestriction

section Gelfand465_part_Work_Gelfand465_Perfect_SmallPieces
open Set MeasureTheory

namespace Gelfand465Perfect

universe u
variable {X : Type u} [MeasurableSpace X]

/-- Genuine atomless splitting: every positive measurable set contains a
measurable subset for which both it and its relative complement have positive
measure. This is genuine positive-set splitting, rather than the singleton-only
condition `NullSingletonClass`; it also excludes nonprincipal measurable atoms. -/
def HasPositiveSplitting (μ : Measure X) : Prop :=
  ∀ s : Set X, MeasurableSet s → 0 < μ s →
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ 0 < μ (s \ t)

variable (μ : Measure X) [IsFiniteMeasure μ] (hsplit : HasPositiveSplitting μ)

include hsplit

/-- Choose the smaller positive half of a genuine measurable split. -/
theorem exists_positive_subset_half (s : Set X) (hs : MeasurableSet s) (hpos : 0 < μ s) :
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ μ.real t ≤ μ.real s / 2 := by
  obtain ⟨t, hts, htm, htpos, hdiffpos⟩ := hsplit s hs hpos
  by_cases ht : μ.real t ≤ μ.real s / 2
  · exact ⟨t, hts, htm, htpos, ht⟩
  · refine ⟨s \ t, sdiff_subset, hs.diff htm, hdiffpos, ?_⟩
    rw [measureReal_sdiff hts htm]
    linarith

/-- Fremlin215D(a): iterative positive splitting gives arbitrarily small
positive pieces, with an explicit dyadic bound. -/
theorem exists_positive_subset_dyadic (s : Set X) (hs : MeasurableSet s)
    (hpos : 0 < μ s) (n : ℕ) :
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧
      μ.real t ≤ (1 / 2 : ℝ) ^ n * μ.real s := by
  induction n with
  | zero => exact ⟨s, Subset.rfl, hs, hpos, by simp⟩
  | succ n ih =>
    obtain ⟨t, hts, htm, htpos, htbound⟩ := ih
    obtain ⟨v, hvt, hvm, hvpos, hvbound⟩ :=
      exists_positive_subset_half μ hsplit t htm htpos
    refine ⟨v, hvt.trans hts, hvm, hvpos, ?_⟩
    calc
      μ.real v ≤ μ.real t / 2 := hvbound
      _ ≤ ((1 / 2 : ℝ) ^ n * μ.real s) / 2 :=
        div_le_div_of_nonneg_right htbound (by norm_num)
      _ = (1 / 2 : ℝ) ^ (n + 1) * μ.real s := by rw [pow_succ]; ring

/-- A truly atomless finite measure has a positive measurable piece below any
prescribed positive real mass, inside every positive measurable set. -/
theorem exists_small_positive_subset (s : Set X) (hs : MeasurableSet s)
    (hpos : 0 < μ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ μ.real t < ε := by
  have hsR : 0 < μ.real s := ENNReal.toReal_pos hpos.ne' (by finiteness)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hsR)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  obtain ⟨t, hts, htm, htpos, htbound⟩ :=
    exists_positive_subset_dyadic μ hsplit s hs hpos n
  exact ⟨t, hts, htm, htpos, htbound.trans_lt ((lt_div_iff₀ hsR).mp hn)⟩

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_SmallPieces

section Gelfand465_part_Work_Gelfand465_Perfect_ExactMass
open Set Filter MeasureTheory
open scoped ENNReal

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

/-- A chain modulo null sets with bounded masses has a measurable upper bound
of the same mass bound, obtained by a countable essential union. -/
theorem ae_chain_upperBound (C : Set (Set X)) (hCm : ∀ s ∈ C, MeasurableSet s)
    (a : ℝ≥0∞) (hbound : ∀ s ∈ C, μ s ≤ a)
    (hchain : ∀ s ∈ C, ∀ t ∈ C, s ≤ᵐ[μ] t ∨ t ≤ᵐ[μ] s) :
    ∃ U : Set X, MeasurableSet U ∧ U ⊆ ⋃₀ C ∧ μ U ≤ a ∧
      ∀ s ∈ C, s ≤ᵐ[μ] U := by
  classical
  obtain ⟨D, hDC, hDc, hD⟩ := μ.exists_ae_subset_biUnion_countable hCm
  refine ⟨⋃₀ D, MeasurableSet.sUnion hDc (fun s hs => hCm s (hDC hs)),
    sUnion_mono hDC, ?_, hD⟩
  rcases D.eq_empty_or_nonempty with rfl | hDne
  · simp
  obtain ⟨r, hr⟩ := hDc.exists_eq_range hDne
  have hrC (n : ℕ) : r n ∈ C := hDC (by rw [hr]; exact mem_range_self n)
  have hacc (n : ℕ) : ∃ k : ℕ, accumulate r n ≤ᵐ[μ] r k := by
    induction n with
    | zero => exact ⟨0, by rw [accumulate_zero_nat]; exact EventuallyLE.rfl⟩
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      rcases hchain (r k) (hrC k) (r (n + 1)) (hrC (n + 1)) with hkn | hnk
      · refine ⟨n + 1, ?_⟩
        rw [accumulate_succ]
        simpa only [union_self] using (hk.trans hkn).union
          (EventuallyLE.rfl : r (n + 1) ≤ᵐ[μ] r (n + 1))
      · refine ⟨k, ?_⟩
        rw [accumulate_succ]
        simpa only [union_self] using hk.union hnk
  rw [hr, sUnion_range, measure_iUnion_eq_iSup_accumulate]
  apply iSup_le
  intro n
  obtain ⟨k, hk⟩ := hacc n
  exact (measure_mono_ae hk).trans (hbound (r k) (hrC k))

/-- The finite-measure exhaustion principle in the bounded-subset case:
there is a maximal member modulo null sets below any prescribed mass. -/
theorem exists_maximal_mass_subset (s : Set X) (a : ℝ≥0∞) :
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ μ t ≤ a ∧
      ∀ v : Set X, v ⊆ s → MeasurableSet v → μ v ≤ a →
        t ≤ᵐ[μ] v → v ≤ᵐ[μ] t := by
  classical
  let H := {t : Set X // t ⊆ s ∧ MeasurableSet t ∧ μ t ≤ a}
  let R : H → H → Prop := fun t v => t.val ≤ᵐ[μ] v.val
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded (r := R) (by
    intro C hC
    let D : Set (Set X) := Subtype.val '' C
    have hDm : ∀ t ∈ D, MeasurableSet t := by
      rintro t ⟨v, hv, rfl⟩
      exact v.property.2.1
    have hDb : ∀ t ∈ D, μ t ≤ a := by
      rintro t ⟨v, hv, rfl⟩
      exact v.property.2.2
    have hDt : ∀ t ∈ D, ∀ v ∈ D, t ≤ᵐ[μ] v ∨ v ≤ᵐ[μ] t := by
      rintro t ⟨b, hb, rfl⟩ v ⟨c, hc, rfl⟩
      by_cases he : b = c
      · subst c
        exact Or.inl EventuallyLE.rfl
      · exact hC hb hc he
    obtain ⟨U, hUm, hUD, hUb, hU⟩ := ae_chain_upperBound μ D hDm a hDb hDt
    have hUs : U ⊆ s := hUD.trans (sUnion_subset (by
      rintro t ⟨v, hv, rfl⟩
      exact v.property.1))
    refine ⟨⟨U, hUs, hUm, hUb⟩, ?_⟩
    intro t ht
    exact hU t.val ⟨t, ht, rfl⟩) (by
      intro b c d hbc hcd
      exact hbc.trans hcd)
  refine ⟨m.val, m.property.1, m.property.2.1, m.property.2.2, ?_⟩
  intro v hvs hvm hva hmv
  exact hm ⟨v, hvs, hvm, hva⟩ hmv

/-- Fremlin215D(b): genuine positive-set splitting gives a measurable subset
of every prescribed mass between zero and that of a finite measurable set. -/
theorem exists_subset_measureReal_eq (hsplit : HasPositiveSplitting μ)
    (s : Set X) (hs : MeasurableSet s) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ μ.real s) :
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧ μ.real t = a := by
  classical
  obtain ⟨t, hts, htm, htbound, hmax⟩ := exists_maximal_mass_subset μ s (ENNReal.ofReal a)
  have hta : μ.real t ≤ a := by
    have h := (ENNReal.toReal_le_toReal (measure_ne_top μ t) ENNReal.ofReal_ne_top).2 htbound
    rw [measureReal_def]
    simpa only [ENNReal.toReal_ofReal ha] using h
  refine ⟨t, hts, htm, le_antisymm hta ?_⟩
  by_contra hnot
  have hlt : μ.real t < a := lt_of_not_ge hnot
  have hdiffR : 0 < μ.real (s \ t) := by
    rw [measureReal_sdiff hts htm]
    linarith
  have hdiff : 0 < μ (s \ t) := by
    exact pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp hdiffR.ne')
  obtain ⟨v, hvsub, hvm, hvpos, hvr⟩ :=
    exists_small_positive_subset μ hsplit (s \ t) (hs.diff htm) hdiff
      (a - μ.real t) (sub_pos.mpr hlt)
  have hdis : Disjoint t v := disjoint_left.mpr (fun x hxt hxv => (hvsub hxv).2 hxt)
  have hunionR : μ.real (t ∪ v) ≤ a := by
    rw [measureReal_union hdis hvm]
    linarith
  have hunion : μ (t ∪ v) ≤ ENNReal.ofReal a := by
    rw [← ofReal_measureReal (μ := μ) (s := t ∪ v)]
    exact ENNReal.ofReal_le_ofReal hunionR
  have hae := hmax (t ∪ v) (union_subset hts (hvsub.trans sdiff_subset))
    (htm.union hvm) hunion (Eventually.of_forall (fun x hx => Or.inl hx))
  have hvdiff : v ⊆ (t ∪ v) \ t := fun x hx => ⟨Or.inr hx, (hvsub hx).2⟩
  have hz : μ v = 0 := measure_mono_null hvdiff (ae_le_set.1 hae)
  exact hvpos.ne' hz

/-- A balanced measurable split, including the zero-mass case. -/
theorem exists_measurable_half (hsplit : HasPositiveSplitting μ)
    (s : Set X) (hs : MeasurableSet s) :
    ∃ t : Set X, t ⊆ s ∧ MeasurableSet t ∧
      μ.real t = μ.real s / 2 ∧ μ.real (s \ t) = μ.real s / 2 := by
  obtain ⟨t, hts, htm, ht⟩ := exists_subset_measureReal_eq μ hsplit s hs (μ.real s / 2)
    (by positivity) (by have h := measureReal_nonneg (μ := μ) (s := s); linarith)
  refine ⟨t, hts, htm, ht, ?_⟩
  rw [measureReal_sdiff hts htm, ht]
  ring

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_ExactMass

section Gelfand465_part_Work_Gelfand465_Perfect_BalancedCells
open Set MeasureTheory

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (hsplit : HasPositiveSplitting μ)

noncomputable def halfSet (s : Set X) (hs : MeasurableSet s) : Set X :=
  (exists_measurable_half μ hsplit s hs).choose

theorem halfSet_spec (s : Set X) (hs : MeasurableSet s) :
    halfSet μ hsplit s hs ⊆ s ∧ MeasurableSet (halfSet μ hsplit s hs) ∧
      μ.real (halfSet μ hsplit s hs) = μ.real s / 2 ∧
      μ.real (s \ halfSet μ hsplit s hs) = μ.real s / 2 :=
  (exists_measurable_half μ hsplit s hs).choose_spec

/-- A list records successive binary choices, with the newest choice first. -/
noncomputable def balancedCell : List Bool → {s : Set X // MeasurableSet s}
  | [] => ⟨univ, MeasurableSet.univ⟩
  | b :: w =>
    let p := balancedCell w
    if b then
      ⟨p.val \ halfSet μ hsplit p.val p.property,
        p.property.diff (halfSet_spec μ hsplit p.val p.property).2.1⟩
    else
      ⟨halfSet μ hsplit p.val p.property,
        (halfSet_spec μ hsplit p.val p.property).2.1⟩

@[simp] theorem balancedCell_nil : (balancedCell μ hsplit []).val = univ := rfl

@[simp] theorem balancedCell_false (w : List Bool) :
    (balancedCell μ hsplit (false :: w)).val =
      halfSet μ hsplit (balancedCell μ hsplit w).val (balancedCell μ hsplit w).property := rfl

@[simp] theorem balancedCell_true (w : List Bool) :
    (balancedCell μ hsplit (true :: w)).val =
      (balancedCell μ hsplit w).val \
        halfSet μ hsplit (balancedCell μ hsplit w).val (balancedCell μ hsplit w).property := rfl

theorem balancedCell_subset_parent (b : Bool) (w : List Bool) :
    (balancedCell μ hsplit (b :: w)).val ⊆ (balancedCell μ hsplit w).val := by
  cases b
  · exact (halfSet_spec μ hsplit (balancedCell μ hsplit w).val (balancedCell μ hsplit w).property).1
  · exact sdiff_subset

theorem balancedCell_child_mass (b : Bool) (w : List Bool) :
    μ.real (balancedCell μ hsplit (b :: w)).val =
      μ.real (balancedCell μ hsplit w).val / 2 := by
  cases b
  · exact (halfSet_spec μ hsplit (balancedCell μ hsplit w).val (balancedCell μ hsplit w).property).2.2.1
  · exact (halfSet_spec μ hsplit (balancedCell μ hsplit w).val (balancedCell μ hsplit w).property).2.2.2

theorem balancedCell_mass (w : List Bool) :
    μ.real (balancedCell μ hsplit w).val =
      (1 / 2 : ℝ) ^ w.length * μ.real univ := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [balancedCell_child_mass, ih, List.length_cons, pow_succ]
    ring

theorem balancedCell_disjoint {v w : List Bool} (hlen : v.length = w.length) (hne : v ≠ w) :
    Disjoint (balancedCell μ hsplit v).val (balancedCell μ hsplit w).val := by
  induction v generalizing w with
  | nil =>
    have hw : w = [] := List.length_eq_zero_iff.mp hlen.symm
    exact (hne hw.symm).elim
  | cons b v ih =>
    cases w with
    | nil => simp at hlen
    | cons c w =>
      have hlen' : v.length = w.length := Nat.succ.inj hlen
      by_cases hvw : v = w
      · subst w
        cases b <;> cases c
        · exact (hne rfl).elim
        · exact disjoint_sdiff_right
        · exact disjoint_sdiff_left
        · exact (hne rfl).elim
      · exact (ih hlen' hvw).mono (balancedCell_subset_parent μ hsplit b v)
          (balancedCell_subset_parent μ hsplit c w)

/-- The unique finite path of a point through the balanced partition. -/
noncomputable def cellPath : ℕ → X → List Bool
  | 0, _ => []
  | n + 1, x => by
    classical
    let p := cellPath n x
    exact if x ∈ halfSet μ hsplit (balancedCell μ hsplit p).val (balancedCell μ hsplit p).property
      then false :: p else true :: p

theorem cellPath_length (n : ℕ) (x : X) : (cellPath μ hsplit n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp only [cellPath]
    split_ifs <;> simpa only [List.length_cons, ih]

theorem mem_balancedCell_cellPath (n : ℕ) (x : X) :
    x ∈ (balancedCell μ hsplit (cellPath μ hsplit n x)).val := by
  induction n with
  | zero => trivial
  | succ n ih =>
    dsimp only [cellPath]
    split_ifs with h
    · exact h
    · exact ⟨ih, h⟩

theorem cellPath_fibre (n : ℕ) (w : List Bool) (hw : w.length = n) :
    {x : X | cellPath μ hsplit n x = w} = (balancedCell μ hsplit w).val := by
  ext x
  constructor
  · intro hx
    rw [← hx]
    exact mem_balancedCell_cellPath μ hsplit n x
  · intro hx
    by_contra hne
    have hd := balancedCell_disjoint μ hsplit
      ((cellPath_length μ hsplit n x).trans hw.symm) hne
    exact Set.disjoint_left.1 hd (mem_balancedCell_cellPath μ hsplit n x) hx

theorem cellPath_fibre_measurable (n : ℕ) (w : List Bool) :
    MeasurableSet {x : X | cellPath μ hsplit n x = w} := by
  by_cases hw : w.length = n
  · rw [cellPath_fibre μ hsplit n w hw]
    exact (balancedCell μ hsplit w).property
  · have he : {x : X | cellPath μ hsplit n x = w} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hx
      exact hw ((congrArg List.length hx).symm.trans (cellPath_length μ hsplit n x))
    rw [he]
    exact MeasurableSet.empty

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_BalancedCells

section Gelfand465_part_Work_Gelfand465_Perfect_RealImage
open Set Filter MeasureTheory
open scoped Topology

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (hsplit : HasPositiveSplitting μ)

include hsplit

noncomputable def pathBit (n : ℕ) (x : X) : Bool :=
  (cellPath μ hsplit (n + 1) x).head!

theorem cellPath_succ (n : ℕ) (x : X) :
    cellPath μ hsplit (n + 1) x = pathBit μ hsplit n x :: cellPath μ hsplit n x := by
  classical
  unfold pathBit
  dsimp only [cellPath]
  split_ifs <;> rfl

theorem measurable_pathBit (n : ℕ) : Measurable (pathBit μ hsplit n) := by
  letI : MeasurableSpace (List Bool) := ⊤
  have hp : Measurable (cellPath μ hsplit (n + 1)) := by
    intro S _
    have he : (cellPath μ hsplit (n + 1)) ⁻¹' S =
        ⋃ w ∈ S, {x : X | cellPath μ hsplit (n + 1) x = w} := by
      ext x
      simp
    rw [he]
    exact MeasurableSet.biUnion (Set.to_countable S)
      (fun w _ => cellPath_fibre_measurable μ hsplit (n + 1) w)
  exact (measurable_from_top (f := fun w : List Bool => w.head!)).comp hp

theorem cellPath_eq_of_bits_eq {x y : X}
    (hbits : ∀ n : ℕ, pathBit μ hsplit n x = pathBit μ hsplit n y) (n : ℕ) :
    cellPath μ hsplit n x = cellPath μ hsplit n y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cellPath_succ, cellPath_succ, hbits n, ih]

/-- A real-valued encoding of the countable sequence of balanced choices. -/
noncomputable def realCellCode (x : X) : ℝ :=
  (cantorSetHomeomorphNatToBool.symm (fun n => pathBit μ hsplit n x)).val

theorem measurable_realCellCode : Measurable (realCellCode μ hsplit) := by
  have hp : Measurable (fun x : X => fun n => pathBit μ hsplit n x) :=
    measurable_pi_lambda _ (fun n => measurable_pathBit μ hsplit n)
  exact measurable_subtype_coe.comp (cantorSetHomeomorphNatToBool.symm.continuous.measurable.comp hp)

theorem cellPath_eq_of_realCellCode_eq {x y : X}
    (hxy : realCellCode μ hsplit x = realCellCode μ hsplit y) (n : ℕ) :
    cellPath μ hsplit n x = cellPath μ hsplit n y := by
  have he : (fun n => pathBit μ hsplit n x) = (fun n => pathBit μ hsplit n y) := by
    apply cantorSetHomeomorphNatToBool.symm.injective
    exact Subtype.ext hxy
  exact cellPath_eq_of_bits_eq μ hsplit (fun k => congrFun he k) n

/-- Every fibre of the real encoding has measure zero, because it is contained
in cells whose masses decrease geometrically to zero. -/
theorem realCellCode_fibre_null (r : ℝ) : μ {x : X | realCellCode μ hsplit x = r} = 0 := by
  let F := {x : X | realCellCode μ hsplit x = r}
  rcases F.eq_empty_or_nonempty with hF | ⟨x, hx⟩
  · change μ F = 0
    rw [hF, measure_empty]
  have hbound (n : ℕ) : μ.real F ≤ (1 / 2 : ℝ) ^ n * μ.real univ := by
    have hsub : F ⊆ (balancedCell μ hsplit (cellPath μ hsplit n x)).val := by
      intro y hy
      have he : cellPath μ hsplit n y = cellPath μ hsplit n x :=
        cellPath_eq_of_realCellCode_eq μ hsplit (hy.trans hx.symm) n
      rw [← he]
      exact mem_balancedCell_cellPath μ hsplit n y
    calc
      μ.real F ≤ μ.real (balancedCell μ hsplit (cellPath μ hsplit n x)).val :=
        measureReal_mono hsub
      _ = (1 / 2 : ℝ) ^ n * μ.real univ := by
        rw [balancedCell_mass, cellPath_length]
  have hlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * μ.real univ) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (μ.real univ)
  have hzero : μ.real F = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) measureReal_nonneg
  exact (measureReal_eq_zero_iff).mp hzero

/-- A finite measure with genuine positive-set splitting has a measurable real
image with zero singleton masses. The real codomain is standard Borel, so this
is the appropriate hypothesis for the CDF probability-integral transform. -/
theorem exists_real_diffuse_map :
    ∃ f : X → ℝ, Measurable f ∧ NullSingletonClass (μ.map f) := by
  refine ⟨realCellCode μ hsplit, measurable_realCellCode μ hsplit, ⟨fun r => ?_⟩⟩
  rw [Measure.map_apply (measurable_realCellCode μ hsplit) (measurableSet_singleton r)]
  exact realCellCode_fibre_null μ hsplit r

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_RealImage

section Gelfand465_part_Work_Gelfand465_Perfect_ProbabilityIntegralTransform
set_option autoImplicit false
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace Gelfand465Perfect

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]

/-- Vanishing singleton masses remove every jump of the canonical CDF. -/
theorem continuous_cdf_of_nullSingleton : Continuous (cdf ν) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf ν).rightLim_eq]
  have hz : (cdf ν).measure {x} = 0 := by
    rw [measure_cdf]
    exact measure_singleton x
  rw [(cdf ν).measure_singleton] at hz
  have hle : cdf ν x ≤ Function.leftLim (cdf ν) x :=
    sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hz)
  exact le_antisymm ((monotone_cdf ν).leftLim_le le_rfl) hle

/-- Every value strictly between zero and one is attained. Flat intervals of
the CDF are allowed; strict monotonicity is not required. -/
theorem exists_cdf_eq_of_mem_Ioo {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ x : ℝ, cdf ν x = t := by
  have h := (isPreconnected_univ : IsPreconnected (univ : Set ℝ)).intermediate_value_Ioo
    (l₁ := atBot) (l₂ := atTop) (by simp) (by simp)
    (continuous_cdf_of_nullSingleton ν).continuousOn
    (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν) ⟨ht0, ht1⟩
  obtain ⟨x, _, hx⟩ := h
  exact ⟨x, hx⟩

/-- The CDF image has the expected cumulative mass inside the unit interval.
The upper bound uses larger attained values, so flat intervals cause no issue. -/
theorem map_cdf_real_Iic {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (ν.map (cdf ν)).real (Iic t) = t := by
  have hf := (continuous_cdf_of_nullSingleton ν).measurable
  letI : IsProbabilityMeasure (ν.map (cdf ν)) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro r htr
    by_cases hr1 : 1 ≤ r
    · exact (measureReal_le_one (μ := ν.map (cdf ν)) (s := Iic t)).trans hr1
    · obtain ⟨y, hy⟩ := exists_cdf_eq_of_mem_Ioo ν (ht0.trans_lt htr) (lt_of_not_ge hr1)
      rw [map_measureReal_apply hf measurableSet_Iic]
      have hs : cdf ν ⁻¹' Iic t ⊆ Iic y := by
        intro z hz
        change cdf ν z ≤ t at hz
        change z ≤ y
        by_contra hzy
        have h := monotone_cdf ν (lt_of_not_ge hzy).le
        rw [hy] at h
        linarith
      calc
        ν.real (cdf ν ⁻¹' Iic t) ≤ ν.real (Iic y) := measureReal_mono hs
        _ = r := (cdf_eq_real ν y).symm.trans hy
  · by_cases ht : t = 0
    · subst t
      exact measureReal_nonneg
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      obtain ⟨y, hy⟩ := exists_cdf_eq_of_mem_Ioo ν htpos ht1
      rw [map_measureReal_apply hf measurableSet_Iic]
      calc
        t = cdf ν y := hy.symm
        _ = ν.real (Iic y) := cdf_eq_real ν y
        _ ≤ ν.real (cdf ν ⁻¹' Iic t) := measureReal_mono (fun z hz =>
          (monotone_cdf ν hz).trans_eq hy)

theorem map_cdf_Iic (t : ℝ) :
    (ν.map (cdf ν)) (Iic t) = ENNReal.ofReal (min t 1) := by
  have hf := (continuous_cdf_of_nullSingleton ν).measurable
  letI : IsProbabilityMeasure (ν.map (cdf ν)) := Measure.isProbabilityMeasure_map hf.aemeasurable
  by_cases ht0 : t < 0
  · have hs : cdf ν ⁻¹' Iic t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact (not_lt_of_ge ((cdf_nonneg ν z).trans hz)) ht0
    rw [Measure.map_apply hf measurableSet_Iic, hs, measure_empty]
    exact (ENNReal.ofReal_eq_zero.mpr ((min_le_left t 1).trans ht0.le)).symm
  · by_cases ht1 : 1 ≤ t
    · have hs : cdf ν ⁻¹' Iic t = univ := by
        ext z
        exact iff_of_true ((cdf_le_one ν z).trans ht1) (mem_univ z)
      rw [Measure.map_apply hf measurableSet_Iic, hs, measure_univ,
        min_eq_right ht1, ENNReal.ofReal_one]
    · calc
        (ν.map (cdf ν)) (Iic t) =
            ENNReal.ofReal ((ν.map (cdf ν)).real (Iic t)) :=
          (ofReal_measureReal (μ := ν.map (cdf ν)) (s := Iic t)).symm
        _ = ENNReal.ofReal t := by
          rw [map_cdf_real_Iic ν (le_of_not_gt ht0) (lt_of_not_ge ht1)]
        _ = ENNReal.ofReal (min t 1) := by rw [min_eq_left (lt_of_not_ge ht1).le]

/-- Probability integral transform for an atomless real probability measure,
using exactly the canonical CDF and Borel Lebesgue restriction to [0,1]. -/
theorem map_cdf_eq_uniform :
    ν.map (cdf ν) = volume.restrict (Icc (0 : ℝ) 1) := by
  have hf := (continuous_cdf_of_nullSingleton ν).measurable
  letI : IsProbabilityMeasure (ν.map (cdf ν)) := Measure.isProbabilityMeasure_map hf.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  rw [map_cdf_Iic ν t, Measure.restrict_apply measurableSet_Iic]
  have hi : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 (min t 1) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [hi, Real.volume_Icc, sub_zero]

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_ProbabilityIntegralTransform

section Gelfand465_part_Work_Gelfand465_Perfect_RationalCuts
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace Gelfand465Perfect
universe u
variable {X : Type u} [TopologicalSpace X] [MeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- Fremlin342L's countable-cut argument. Inner approximation by measurable
closed sets suffices; no separation axiom or Borel compatibility on the source
is required. Rational intervals replace rational half-lines in the same argument. -/
theorem exists_closed_continuousOn_positive
    (hreg : μ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet)
    (f : X → ℝ) (hf : Measurable f) {E : Set X} (hE : MeasurableSet E)
    (hpos : 0 < μ E) :
    ∃ C : Set X, C ⊆ E ∧ IsClosed C ∧ MeasurableSet C ∧
      0 < μ C ∧ ContinuousOn f C := by
  classical
  let I := (ℚ × ℚ) × Bool
  let A : I → Set X := fun i =>
    if i.2 then E \ f ⁻¹' Ioo (i.1.1 : ℝ) (i.1.2 : ℝ)
    else E ∩ f ⁻¹' Ioo (i.1.1 : ℝ) (i.1.2 : ℝ)
  have hA (i : I) : MeasurableSet (A i) := by
    dsimp [A]
    split_ifs
    · exact hE.diff (hf measurableSet_Ioo)
    · exact hE.inter (hf measurableSet_Ioo)
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hpos.ne' I
  have happrox (i : I) : ∃ k, k ⊆ A i ∧ IsClosed k ∧ MeasurableSet k ∧
      μ (A i \ k) < δ i := by
    obtain ⟨k, hki, ⟨hkc, hkm⟩, hkμ⟩ := hreg.exists_subset_lt_add
      ⟨isClosed_empty, MeasurableSet.empty⟩ (hA i) (measure_ne_top μ _) (hδpos i).ne'
    exact ⟨k, hki, hkc, hkm,
      measure_sdiff_lt_of_lt_add hkm.nullMeasurableSet hki (measure_ne_top μ _) hkμ⟩
  choose k hkA hkc hkm hkμ using happrox
  let C : Set X := ⋂ q : ℚ × ℚ, k (q, false) ∪ k (q, true)
  have hCE : C ⊆ E := by
    intro x hx
    have hx' := mem_iInter.mp hx ((0, 0) : ℚ × ℚ)
    rcases hx' with hx' | hx'
    · exact (hkA _ hx').1
    · exact (hkA _ hx').1
  have hCc : IsClosed C := isClosed_iInter (fun q => (hkc (q, false)).union (hkc (q, true)))
  have hCm : MeasurableSet C := MeasurableSet.iInter
    (fun q => (hkm (q, false)).union (hkm (q, true)))
  have hloss : E \ C ⊆ ⋃ i : I, A i \ k i := by
    intro x hx
    have hex : ∃ q : ℚ × ℚ, x ∉ k (q, false) ∪ k (q, true) := by
      simpa only [C, mem_iInter, not_forall] using hx.2
    obtain ⟨q, hq⟩ := hex
    by_cases hxq : x ∈ f ⁻¹' Ioo (q.1 : ℝ) (q.2 : ℝ)
    · refine mem_iUnion.mpr ⟨(q, false), ?_⟩
      exact ⟨⟨hx.1, hxq⟩, fun hk => hq (Or.inl hk)⟩
    · refine mem_iUnion.mpr ⟨(q, true), ?_⟩
      exact ⟨⟨hx.1, hxq⟩, fun hk => hq (Or.inr hk)⟩
  have hlossμ : μ (E \ C) < μ E :=
    ((measure_mono hloss).trans
      ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum (fun i => (hkμ i).le)))).trans_lt hδsum
  have hCpos : 0 < μ C := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have heq : μ (E \ C) = μ E := measure_sdiff_null hzero
    exact (lt_irrefl (μ E)) (heq ▸ hlossμ)
  refine ⟨C, hCE, hCc, hCm, hCpos, ?_⟩
  apply Real.isTopologicalBasis_Ioo_rat.continuousOn_iff.mpr
  intro U hU
  simp only [mem_iUnion, mem_singleton_iff] at hU
  obtain ⟨a, b, _, rfl⟩ := hU
  refine ⟨(k ((a, b), true))ᶜ, (hkc _).isOpen_compl, ?_⟩
  ext x
  constructor
  · rintro ⟨hxU, hxC⟩
    exact ⟨fun hxk => (hkA _ hxk).2 hxU, hxC⟩
  · rintro ⟨hxk, hxC⟩
    have hxunion := mem_iInter.mp hxC (a, b)
    rcases hxunion with hxf | hxt
    · exact ⟨(hkA _ hxf).2, hxC⟩
    · exact False.elim (hxk hxt)

/-- A finite measure inner regular for measurable closed sets in a compact
topology satisfies the compact-image formulation of perfectness. -/
theorem exists_compact_positive_image [CompactSpace X]
    (hreg : μ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet)
    (f : X → ℝ) (hf : Measurable f) {E : Set X} (hE : MeasurableSet E)
    (hpos : 0 < μ E) :
    ∃ K : Set ℝ, IsCompact K ∧ K ⊆ f '' E ∧ 0 < μ (f ⁻¹' K ∩ E) := by
  obtain ⟨C, hCE, hCc, _, hCμ, hfC⟩ := exists_closed_continuousOn_positive μ hreg f hf hE hpos
  refine ⟨f '' C, hCc.isCompact.image_of_continuousOn hfC, image_mono hCE, ?_⟩
  exact hCμ.trans_le (measure_mono (fun x hx => ⟨mem_image_of_mem f hx, hCE hx⟩))

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_RationalCuts

section Gelfand465_part_Work_Gelfand465_Perfect_PowerSetImage
open Set MeasureTheory

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (f : X → ℝ) (hf : Measurable f)

include hf

/-- A measurable core of an arbitrary image set, modulo its inverse-image
measure. This is the compact-core step in Fremlin451Q(b); compactness of the
pushforward measure is not assumed. -/
theorem exists_measurable_image_core
    (hperfect : ∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ f '' E ∧ 0 < μ (f ⁻¹' K ∩ E))
    (hpre : ∀ S : Set ℝ, MeasurableSet (f ⁻¹' S)) (S : Set ℝ) :
    ∃ U : Set ℝ, MeasurableSet U ∧ U ⊆ S ∧ μ (f ⁻¹' (S \ U)) = 0 := by
  let C : Set (Set ℝ) := {K | IsCompact K ∧ K ⊆ S}
  obtain ⟨D, hDC, hDc, hD⟩ := (μ.map f).exists_ae_subset_biUnion_countable
    (C := C) (fun K hK => hK.1.measurableSet)
  have hDm : MeasurableSet (⋃₀ D) :=
    MeasurableSet.sUnion hDc (fun K hK => (hDC hK).1.measurableSet)
  refine ⟨⋃₀ D, hDm, sUnion_subset (fun K hK => (hDC hK).2), ?_⟩
  by_contra hne
  obtain ⟨K, hKc, hKimage, hKpos⟩ := hperfect (f ⁻¹' (S \ ⋃₀ D))
    (hpre _) (pos_iff_ne_zero.mpr hne)
  have hKS : K ⊆ S \ ⋃₀ D := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hKimage hy
    exact hx
  have hzero := ae_le_set.1 (hD K ⟨hKc, hKS.trans sdiff_subset⟩)
  have hdiff : K \ ⋃₀ D = K := by
    ext y
    exact ⟨fun hy => hy.1, fun hy => ⟨hy, (hKS hy).2⟩⟩
  rw [hdiff, Measure.map_apply hf hKc.measurableSet] at hzero
  have hle : μ (f ⁻¹' K ∩ f ⁻¹' (S \ ⋃₀ D)) ≤ 0 :=
    (measure_mono inter_subset_left).trans_eq hzero
  exact (not_lt_of_ge hle) hKpos

/-- Perfectness and measurability of every real-set inverse image force every
real set to lie in the completion of the ordinary Borel pushforward. Applying
the compact-core lemma to both a set and its complement is essential here. -/
theorem all_nullMeasurable_map_of_perfect
    (hperfect : ∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ f '' E ∧ 0 < μ (f ⁻¹' K ∩ E))
    (hpre : ∀ S : Set ℝ, MeasurableSet (f ⁻¹' S)) (S : Set ℝ) :
    NullMeasurableSet S (μ.map f) := by
  obtain ⟨U, hUm, hUS, hU0⟩ := exists_measurable_image_core μ f hf hperfect hpre S
  obtain ⟨V, hVm, hVS, hV0⟩ := exists_measurable_image_core μ f hf hperfect hpre Sᶜ
  have hres : μ (f ⁻¹' (U ∪ V)ᶜ) = 0 := by
    apply measure_mono_null (t := (f ⁻¹' (S \ U)) ∪ (f ⁻¹' (Sᶜ \ V)))
    · intro x hx
      change f x ∉ U ∪ V at hx
      by_cases hs : f x ∈ S
      · exact Or.inl ⟨hs, fun h => hx (Or.inl h)⟩
      · exact Or.inr ⟨hs, fun h => hx (Or.inr h)⟩
    · exact measure_union_null hU0 hV0
  have hres' : (μ.map f) (U ∪ V)ᶜ = 0 := by
    rw [Measure.map_apply hf (hUm.union hVm).compl]
    exact hres
  have hSU : (μ.map f) (S \ U) = 0 := by
    apply measure_mono_null (t := (U ∪ V)ᶜ) ?_ hres'
    intro x hx
    rintro (hU | hV)
    · exact hx.2 hU
    · exact hVS hV hx.1
  apply hUm.nullMeasurableSet.congr
  exact ae_eq_set.2 ⟨by rw [sdiff_eq_empty.mpr hUS, measure_empty], hSU⟩

/-- In this situation the Borel pushforward also has the expected value on
every subset, because all subsets are measurable for its completion. -/
theorem map_apply_of_perfect_all_preimages
    (hperfect : ∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ f '' E ∧ 0 < μ (f ⁻¹' K ∩ E))
    (hpre : ∀ S : Set ℝ, MeasurableSet (f ⁻¹' S)) (S : Set ℝ) :
    (μ.map f) S = μ (f ⁻¹' S) :=
  Measure.map_apply₀ hf.aemeasurable
    (all_nullMeasurable_map_of_perfect μ f hf hperfect hpre S)

/-- The preceding consequence applies to the compact topology and closed-set
inner regularity constructed from the canonical compact enhanced predicate. -/
theorem all_nullMeasurable_map_of_closed_innerRegular [TopologicalSpace X] [CompactSpace X]
    (hreg : μ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet)
    (hpre : ∀ S : Set ℝ, MeasurableSet (f ⁻¹' S)) (S : Set ℝ) :
    NullMeasurableSet S (μ.map f) :=
  all_nullMeasurable_map_of_perfect μ f hf
    (fun E hE hpos => exists_compact_positive_image μ hreg f hf hE hpos) hpre S

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_PowerSetImage

section Gelfand465_part_Work_Gelfand465_Perfect_PerfectOperations
open Set MeasureTheory
open scoped ENNReal

namespace Gelfand465Perfect
universe u v
variable {X : Type u} [MeasurableSpace X]

/-- The compact-image formulation of finite-measure perfectness already proved
from the canonical compact enhanced-space hypothesis. -/
def HasPerfectRealImages (μ : Measure X) : Prop :=
  ∀ f : X → ℝ, Measurable f →
    ∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ f '' E ∧ 0 < μ (f ⁻¹' K ∩ E)

namespace HasPerfectRealImages
variable {μ : Measure X}

/-- Perfectness passes to measurable images; this asserts perfectness, not
compactness, of the image measure. -/
theorem map (hμ : HasPerfectRealImages μ) {Y : Type v} [MeasurableSpace Y]
    (π : X → Y) (hπ : Measurable π) : HasPerfectRealImages (μ.map π) := by
  intro f hf E hE hpos
  have hpos' : 0 < μ (π ⁻¹' E) := by
    rwa [Measure.map_apply hπ hE] at hpos
  obtain ⟨K, hK, hKE, hKpos⟩ := hμ (f ∘ π) (hf.comp hπ) (π ⁻¹' E) (hπ hE) hpos'
  refine ⟨K, hK, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hKE hy
    exact ⟨π x, hx, rfl⟩
  · rw [Measure.map_apply hπ ((hf hK.measurableSet).inter hE)]
    simpa only [preimage_inter, preimage_comp] using hKpos

theorem restrict (hμ : HasPerfectRealImages μ) (S : Set X) (hS : MeasurableSet S) :
    HasPerfectRealImages (μ.restrict S) := by
  intro f hf E hE hpos
  have hpos' : 0 < μ (E ∩ S) := by rwa [Measure.restrict_apply hE] at hpos
  obtain ⟨K, hK, hKE, hKpos⟩ := hμ f hf (E ∩ S) (hE.inter hS) hpos'
  refine ⟨K, hK, hKE.trans (image_mono inter_subset_left), ?_⟩
  rw [Measure.restrict_apply ((hf hK.measurableSet).inter hE)]
  simpa only [inter_assoc] using hKpos

theorem smul (hμ : HasPerfectRealImages μ) (c : ℝ≥0∞) (hc : 0 < c) :
    HasPerfectRealImages (c • μ) := by
  intro f hf E hE hpos
  rw [Measure.smul_apply] at hpos
  change 0 < c * μ E at hpos
  obtain ⟨K, hK, hKE, hKpos⟩ := hμ f hf E hE ((ENNReal.mul_pos_iff).1 hpos).2
  refine ⟨K, hK, hKE, ?_⟩
  rw [Measure.smul_apply]
  exact (ENNReal.mul_pos_iff).2 ⟨hc, hKpos⟩

end HasPerfectRealImages

/-- Genuine splitting survives multiplication by a positive scalar. -/
theorem HasPositiveSplitting.smul {μ : Measure X} (hμ : HasPositiveSplitting μ)
    (c : ℝ≥0∞) (hc : 0 < c) : HasPositiveSplitting (c • μ) := by
  intro s hs hpos
  rw [Measure.smul_apply] at hpos
  change 0 < c * μ s at hpos
  obtain ⟨t, hts, htm, ht, hdiff⟩ := hμ s hs ((ENNReal.mul_pos_iff).1 hpos).2
  refine ⟨t, hts, htm, ?_, ?_⟩
  · rw [Measure.smul_apply]
    exact (ENNReal.mul_pos_iff).2 ⟨hc, ht⟩
  · rw [Measure.smul_apply]
    exact (ENNReal.mul_pos_iff).2 ⟨hc, hdiff⟩

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_PerfectOperations

section Gelfand465_part_Work_Gelfand465_Perfect_Vitali
open Set MeasureTheory Bornology
open scoped Pointwise

namespace Gelfand465Perfect

/-- Rational-translation equivalence restricted to a given set. -/
def rationalSetoid (A : Set ℝ) : Setoid A where
  r x y := ∃ q : ℚ, (x : ℝ) - y = (q : ℝ)
  iseqv := {
    refl := fun x => ⟨0, by simp⟩
    symm := by
      rintro x y ⟨q, hq⟩
      refine ⟨-q, ?_⟩
      push_cast
      linarith
    trans := by
      rintro x y z ⟨q, hq⟩ ⟨r, hr⟩
      refine ⟨q + r, ?_⟩
      push_cast
      linarith }

/-- One representative of every rational-translation class meeting `A`. -/
noncomputable def vitaliSelector (A : Set ℝ) : Set ℝ :=
  Set.range (fun q : Quotient (rationalSetoid A) => (q.out : ℝ))

lemma vitaliSelector_subset (A : Set ℝ) : vitaliSelector A ⊆ A := by
  rintro x ⟨q, rfl⟩
  exact q.out.property

lemma vitaliSelector_unique (A : Set ℝ) {x y : ℝ}
    (hx : x ∈ vitaliSelector A) (hy : y ∈ vitaliSelector A)
    (hxy : ∃ q : ℚ, x - y = (q : ℝ)) : x = y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a = b := by
    calc
      a = Quotient.mk (rationalSetoid A) a.out := (Quotient.out_eq a).symm
      _ = Quotient.mk (rationalSetoid A) b.out := Quotient.sound hxy
      _ = b := Quotient.out_eq b
  exact congrArg (fun q : Quotient (rationalSetoid A) => (q.out : ℝ)) hab

lemma vitaliSelector_disjoint_translates (A : Set ℝ) :
    Pairwise (fun q r : ℚ =>
      Disjoint ({(q : ℝ)} + vitaliSelector A) ({(r : ℝ)} + vitaliSelector A)) := by
  intro q r hqr
  apply Set.disjoint_left.2
  intro z hzq hzr
  rw [singleton_add] at hzq hzr
  obtain ⟨x, hx, hxz⟩ := hzq
  obtain ⟨y, hy, hyz⟩ := hzr
  have hxy : x = y := vitaliSelector_unique A hx hy ⟨r - q, by push_cast; linarith⟩
  apply hqr
  apply Rat.cast_injective (α := ℝ)
  linarith

lemma subset_iUnion_vitaliSelector_translates (A : Set ℝ) :
    A ⊆ ⋃ q : ℚ, {(q : ℝ)} + vitaliSelector A := by
  intro x hx
  let a : A := ⟨x, hx⟩
  let c : Quotient (rationalSetoid A) := Quotient.mk _ a
  have hrel : (rationalSetoid A).r a c.out :=
    Quotient.exact (Quotient.out_eq c).symm
  obtain ⟨q, hq⟩ := hrel
  apply Set.mem_iUnion.2
  refine ⟨q, ?_⟩
  rw [singleton_add]
  refine ⟨(c.out : ℝ), ⟨c, rfl⟩, ?_⟩
  change x - (c.out : ℝ) = (q : ℝ) at hq
  linarith

/-- Fremlin 134B/134X(c): a positive set contains a subset outside the completed
Lebesgue sigma-algebra. The selector supplies disjoint rational translates;
Mathlib's Haar-measure theorem supplies the finite-volume contradiction. -/
theorem exists_not_nullMeasurable_subset (A : Set ℝ) (hA : volume A ≠ 0) :
    ∃ V : Set ℝ, V ⊆ A ∧ ¬NullMeasurableSet V volume := by
  classical
  let V := vitaliSelector A
  have hdisj := vitaliSelector_disjoint_translates A
  have hV : volume V ≠ 0 := by
    intro hz
    apply hA
    apply measure_mono_null (subset_iUnion_vitaliSelector_translates A)
    apply measure_iUnion_null
    intro q
    simpa only [singleton_add, image_add_left, measure_preimage_add] using hz
  refine ⟨V, vitaliSelector_subset A, ?_⟩
  intro hVm
  obtain ⟨W, hWV, hWm, hWVae⟩ := hVm.exists_measurable_subset_ae_eq
  let e : ℕ ↪ Set.Icc (0 : ℚ) 1 :=
    Set.Infinite.natEmbedding _ (Set.Icc_infinite (by norm_num))
  let u : ℕ → ℝ := fun n => ((e n).val : ℝ)
  have hu : IsBounded (Set.range u) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rintro x ⟨n, rfl⟩
    constructor
    · change (0 : ℝ) ≤ ((e n).val : ℝ)
      exact_mod_cast (e n).property.1
    · change ((e n).val : ℝ) ≤ (1 : ℝ)
      exact_mod_cast (e n).property.2
  have hWzero : volume W = 0 := by
    apply Measure.addHaar_eq_zero_of_disjoint_translates volume u hu _ hWm
    intro n m hnm
    have hne : (e n).val ≠ (e m).val := by
      intro h
      exact hnm (e.injective (Subtype.ext h))
    exact (hdisj hne).mono
      (add_subset_add Subset.rfl hWV) (add_subset_add Subset.rfl hWV)
  exact hV ((measure_congr hWVae).symm.trans hWzero)

/-- The same obstruction holds for Lebesgue measure restricted to any set of
positive measure. No measurability assumption on the ambient set is needed. -/
theorem exists_not_nullMeasurable_restrict_subset (A : Set ℝ) (hA : volume A ≠ 0) :
    ∃ V : Set ℝ, V ⊆ A ∧ ¬NullMeasurableSet V (volume.restrict A) := by
  obtain ⟨V, hVA, hV⟩ := exists_not_nullMeasurable_subset A hA
  exact ⟨V, hVA, fun h => hV ((nullMeasurableSet_restrict_of_subset hVA).1 h)⟩

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_Vitali

section Gelfand465_part_Work_Gelfand465_Perfect_UniformObstruction
open Set MeasureTheory

namespace Gelfand465Perfect

/-- The contradiction at the end of Fremlin451Q(b), after a uniform image has
been constructed. Construction of that image from a truly atomless measure is
not asserted here. -/
theorem no_uniform_map_of_perfect {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hperfect : ∀ E : Set X, MeasurableSet E → 0 < μ E →
      ∃ K : Set ℝ, IsCompact K ∧ K ⊆ f '' E ∧ 0 < μ (f ⁻¹' K ∩ E))
    (hpre : ∀ S : Set ℝ, MeasurableSet (f ⁻¹' S))
    (A : Set ℝ) (hA : volume A ≠ 0) : μ.map f ≠ volume.restrict A := by
  intro hmap
  obtain ⟨V, _, hV⟩ := exists_not_nullMeasurable_restrict_subset A hA
  apply hV
  rw [← hmap]
  exact all_nullMeasurable_map_of_perfect μ f hf hperfect hpre V

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_UniformObstruction

section Gelfand465_part_Work_Gelfand465_Perfect_AtomlessObstruction
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X]

/-- The atomless contradiction in Fremlin451Q(b), for a probability measure on
an entire power set. The positive-set splitting premise is genuine atomlessness. -/
theorem not_splitting_perfect_powerset_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (hperfect : HasPerfectRealImages μ) (hall : ∀ s : Set X, MeasurableSet s) :
    ¬HasPositiveSplitting μ := by
  intro hsplit
  obtain ⟨f, hf, hdiffuse⟩ := exists_real_diffuse_map μ hsplit
  let ν := μ.map f
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : NullSingletonClass ν := hdiffuse
  have hcdf : Measurable (cdf ν) := (continuous_cdf_of_nullSingleton ν).measurable
  let g : X → ℝ := cdf ν ∘ f
  have hg : Measurable g := hcdf.comp hf
  have hmap : μ.map g = volume.restrict (Icc (0 : ℝ) 1) := by
    rw [← Measure.map_map hcdf hf]
    exact map_cdf_eq_uniform ν
  apply no_uniform_map_of_perfect μ g hg (hperfect g hg)
    (fun S => hall (g ⁻¹' S)) (Icc (0 : ℝ) 1) ?_ hmap
  simp [Real.volume_Icc]

/-- Normalization reduces the nonzero finite-measure case to probability. -/
theorem not_splitting_perfect_powerset (μ : Measure X) [IsFiniteMeasure μ] (hne : μ ≠ 0)
    (hperfect : HasPerfectRealImages μ) (hall : ∀ s : Set X, MeasurableSet s) :
    ¬HasPositiveSplitting μ := by
  intro hsplit
  letI : NeZero μ := ⟨hne⟩
  let c : ℝ≥0∞ := (μ univ)⁻¹
  have hc : 0 < c := ENNReal.inv_pos.mpr (measure_ne_top μ univ)
  exact not_splitting_perfect_powerset_probability (c • μ)
    (hperfect.smul c hc) hall (hsplit.smul c hc)

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_AtomlessObstruction

section Gelfand465_part_Work_Gelfand465_Perfect_AtomUltrafilter
open Set Filter MeasureTheory
open scoped ENNReal

namespace Gelfand465Perfect
universe u
variable {X : Type u} [MeasurableSpace X]

/-- A positive measurable atom, allowing nonprincipal atoms. -/
def IsPositiveMeasureAtom (μ : Measure X) (A : Set X) : Prop :=
  MeasurableSet A ∧ 0 < μ A ∧
    ∀ s : Set X, s ⊆ A → MeasurableSet s → μ s = 0 ∨ μ (A \ s) = 0

/-- Failure of genuine splitting supplies a positive measurable atom, not a
point of positive mass. -/
theorem exists_positiveMeasureAtom_of_not_splitting (μ : Measure X)
    (hnot : ¬HasPositiveSplitting μ) : ∃ A : Set X, IsPositiveMeasureAtom μ A := by
  classical
  by_contra h
  apply hnot
  intro s hs hpos
  by_contra hnosplit
  apply h
  refine ⟨s, hs, hpos, ?_⟩
  intro t hts htm
  by_cases ht : μ t = 0
  · exact Or.inl ht
  · right
    by_contra hdiff
    exact hnosplit ⟨t, hts, htm, pos_iff_ne_zero.mpr ht, pos_iff_ne_zero.mpr hdiff⟩

namespace IsPositiveMeasureAtom
variable {μ : Measure X} {A : Set X} (hA : IsPositiveMeasureAtom μ A)
  (hall : ∀ s : Set X, MeasurableSet s)

include hA hall

theorem restrict_dichotomy (s : Set X) :
    (μ.restrict A) s = 0 ∨ (μ.restrict A) sᶜ = 0 := by
  rw [Measure.restrict_apply (hall s), Measure.restrict_apply (hall sᶜ)]
  have h := hA.2.2 (s ∩ A) inter_subset_right (hall (s ∩ A))
  have he : A \ (s ∩ A) = sᶜ ∩ A := by ext x; simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff]; tauto
  rwa [he] at h

/-- On a measurable power set, the conull filter of an atom is an ultrafilter.
This construction makes no claim that the corresponding source measure is atomic. -/
noncomputable def ultrafilter : Ultrafilter X :=
  Ultrafilter.ofComplNotMemIff (ae (μ.restrict A)) (by
    intro s
    simp only [mem_ae_iff, compl_compl]
    constructor
    · intro hs
      exact (hA.restrict_dichotomy hall s).resolve_left hs
    · intro hs hz
      have hzero : (μ.restrict A) univ = 0 := by
        simpa only [union_compl_self] using measure_union_null hz hs
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hzero
      exact hA.2.1.ne' hzero)

@[simp]
theorem ultrafilter_toFilter : (hA.ultrafilter hall : Filter X) = ae (μ.restrict A) := rfl

instance ultrafilter_countableInter : CountableInterFilter (hA.ultrafilter hall : Filter X) := by
  change CountableInterFilter (ae (μ.restrict A))
  infer_instance

/-- If all singleton masses vanish, this countably complete ultrafilter is
nonprincipal. The atom may therefore genuinely be a nonprincipal index atom. -/
theorem ultrafilter_ne_pure [NullSingletonClass μ] (x : X) :
    hA.ultrafilter hall ≠ pure x := by
  intro he
  have hx : {x} ∈ hA.ultrafilter hall := by rw [he]; simp
  have hc : {x}ᶜ ∈ hA.ultrafilter hall := by
    change {x}ᶜ ∈ ae (μ.restrict A)
    rw [compl_mem_ae_iff, Measure.restrict_apply (hall {x})]
    exact measure_mono_null inter_subset_left (measure_singleton x)
  exact Filter.compl_notMem hx hc

end IsPositiveMeasureAtom
end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_AtomUltrafilter

section Gelfand465_part_Work_Gelfand465_Perfect_UltrafilterNormalization
open Set Filter

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {Y : Type v}

/-- Countable intersection closure rules out a descending sequence of
well-order-valued functions modulo a nontrivial filter (Fremlin4A1K(b)). -/
theorem wellFounded_eventually_lt (F : Filter X) [F.NeBot] [CountableInterFilter F]
    [LT Y] [WellFoundedLT Y] :
    WellFounded (fun f g : X → Y => ∀ᶠ x in F, f x < g x) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨?_⟩
  intro h
  obtain ⟨x, hx⟩ := Filter.Eventually.exists (eventually_countable_forall.mpr h.property)
  exact (wellFounded_iff_isEmpty_descending_chain.mp wellFounded_lt).false
    ⟨fun n => h.val n x, hx⟩

/-- A minimal nonconstant function modulo a countably complete ultrafilter
produces the pressing-down property. No regular-cardinal premise is inserted. -/
theorem exists_pressingDown_image (F : Ultrafilter X) [CountableInterFilter (F : Filter X)]
    [LinearOrder Y] [WellFoundedLT Y] (f₀ : X → Y)
    (hf₀ : ∀ y : Y, {x | f₀ x = y} ∉ F) :
    ∃ g : X → Y, (∀ y : Y, {x | g x = y} ∉ F) ∧
      ∀ h : Y → Y, (∀ᶠ y in (F.map g : Filter Y), h y < y) →
        ∃ a : Y, ∀ᶠ y in (F.map g : Filter Y), h y = a := by
  classical
  let H : Set (X → Y) := {g | ∀ y : Y, {x | g x = y} ∉ F}
  obtain ⟨g, hg, hmin⟩ := (wellFounded_eventually_lt (F : Filter X)).has_min H ⟨f₀, hf₀⟩
  refine ⟨g, hg, ?_⟩
  intro h hreg
  by_contra hconstant
  have hh : (h ∘ g) ∈ H := by
    intro a
    exact not_exists.mp hconstant a
  exact hmin (h ∘ g) hh hreg

/-- The pressing-down property gives closure under diagonal intersections,
the exact combinatorial input to the finite-set homogeneity induction. -/
theorem diagonal_mem_of_pressingDown (F : Ultrafilter Y) [LinearOrder Y]
    (hpress : ∀ h : Y → Y, (∀ᶠ y in (F : Filter Y), h y < y) →
      ∃ a : Y, ∀ᶠ y in (F : Filter Y), h y = a)
    (A : Y → Set Y) (hA : ∀ a, A a ∈ F) :
    {y | ∀ a < y, y ∈ A a} ∈ F := by
  classical
  by_contra hdiag
  have hbad : ∀ᶠ y in (F : Filter Y), ∃ a, a < y ∧ y ∉ A a := by
    have hc := F.compl_mem_iff_notMem.mpr hdiag
    filter_upwards [hc] with y hy
    change ¬∀ a, a < y → y ∈ A a at hy
    obtain ⟨a, ha⟩ := not_forall.mp hy
    exact ⟨a, (_root_.not_imp.mp ha).1, (_root_.not_imp.mp ha).2⟩
  obtain ⟨y₀, _⟩ := F.nonempty_of_mem (s := univ) Filter.univ_mem
  let h : Y → Y := fun y => if hy : ∃ a, a < y ∧ y ∉ A a then hy.choose else y₀
  have hh : ∀ᶠ y in (F : Filter Y), h y < y ∧ y ∉ A (h y) := by
    filter_upwards [hbad] with y hy
    simpa only [h, dif_pos hy] using hy.choose_spec
  obtain ⟨a, ha⟩ := hpress h (hh.mono fun _ hy => hy.1)
  have hfalse : ∀ᶠ y in (F : Filter Y), False := by
    filter_upwards [hh, ha, hA a] with y hy hya hmem
    exact hy.2 (hya.symm ▸ hmem)
  exact hfalse.exists.elim fun _ hx => hx

/-- A diffuse ultrafilter on a well-order has a large initial domain on which
all upper tails are large. No cardinal-regularity machinery is needed. -/
theorem exists_large_tail_domain (F : Ultrafilter Y) [LinearOrder Y] [WellFoundedLT Y]
    (hdiffuse : ∀ y : Y, {y} ∉ F) :
    ∃ S : Set Y, S ∈ F ∧ ∀ a ∈ S, Ioi a ∈ F := by
  classical
  by_cases hex : ∃ b : Y, Iic b ∈ F
  · obtain ⟨b, hb, hmin⟩ := wellFounded_lt.has_min {b : Y | Iic b ∈ F} hex
    refine ⟨Iio b, ?_, ?_⟩
    · have hc : ({b} : Set Y)ᶜ ∈ F := F.compl_mem_iff_notMem.mpr (hdiffuse b)
      filter_upwards [hb, hc] with y hy hyn
      exact lt_of_le_of_ne hy (by simpa only [mem_compl_iff, mem_singleton_iff] using hyn)
    · intro a ha
      have hn : Iic a ∉ F := fun h => hmin a h ha
      simpa only [compl_Iic] using F.compl_mem_iff_notMem.mpr hn
  · refine ⟨univ, Filter.univ_mem, ?_⟩
    intro a _
    have hn : Iic a ∉ F := fun h => hex ⟨a, h⟩
    simpa only [compl_Iic] using F.compl_mem_iff_notMem.mpr hn

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_UltrafilterNormalization

section Gelfand465_part_Work_Gelfand465_Perfect_UltrafilterHomogeneity
set_option autoImplicit false
open Set Filter

namespace Gelfand465Perfect
universe u
variable {Y : Type u} [LinearOrder Y]

/-- Diagonal closure of an ultrafilter gives a homogeneous large set for each
fixed finite cardinality. -/
theorem exists_homogeneous_card (F : Ultrafilter Y)
    (hdiag : ∀ A : Y → Set Y, (∀ a, A a ∈ F) →
      {y | ∀ a < y, y ∈ A a} ∈ F)
    (n : ℕ) (P : Finset Y → Prop) :
    ∃ S : Set Y, S ∈ F ∧
      ((∀ t : Finset Y, (↑t : Set Y) ⊆ S → t.card = n → P t) ∨
       (∀ t : Finset Y, (↑t : Set Y) ⊆ S → t.card = n → ¬ P t)) := by
  classical
  induction n generalizing P with
  | zero =>
    by_cases hp : P ∅
    · refine ⟨univ, univ_mem, Or.inl ?_⟩
      intro t _ ht
      have he : t = ∅ := Finset.card_eq_zero.mp ht
      simpa only [he] using hp
    · refine ⟨univ, univ_mem, Or.inr ?_⟩
      intro t _ ht
      have he : t = ∅ := Finset.card_eq_zero.mp ht
      simpa only [he] using hp
  | succ n ih =>
    choose S hS hHom using fun a : Y => ih (fun t => P (insert a t))
    let D : Set Y := {y | ∀ a < y, y ∈ S a}
    have hD : D ∈ F := hdiag S hS
    let A : Set Y := {a | ∀ t : Finset Y,
      (↑t : Set Y) ⊆ S a → t.card = n → P (insert a t)}
    have hreduce (H : Set Y) (hHD : H ⊆ D) (t : Finset Y)
        (htH : (↑t : Set Y) ⊆ H) (htcard : t.card = n + 1) :
        ∃ a : Y, a ∈ H ∧ (↑(t.erase a) : Set Y) ⊆ S a ∧
          (t.erase a).card = n ∧ insert a (t.erase a) = t := by
      have htne : t.Nonempty := Finset.card_pos.mp (by omega)
      let a : Y := t.min' htne
      have ha : a ∈ t := Finset.min'_mem t htne
      refine ⟨a, htH ha, ?_, ?_, Finset.insert_erase ha⟩
      · intro b hb
        have hbt : b ∈ t := (Finset.mem_erase.mp hb).2
        have hba : b ≠ a := (Finset.mem_erase.mp hb).1
        have hab : a ≤ b := Finset.min'_le t b hbt
        exact (hHD (htH hbt)) a (lt_of_le_of_ne hab (Ne.symm hba))
      · rw [Finset.card_erase_of_mem ha, htcard]
        omega
    rcases F.mem_or_compl_mem A with hA | hA
    · refine ⟨D ∩ A, inter_mem hD hA, Or.inl ?_⟩
      intro t ht htcard
      obtain ⟨a, ha, hsub, hcard, heq⟩ := hreduce (D ∩ A) inter_subset_left t ht htcard
      have hpos := ha.2 (t.erase a) hsub hcard
      simpa only [heq] using hpos
    · refine ⟨D ∩ Aᶜ, inter_mem hD hA, Or.inr ?_⟩
      intro t ht htcard
      obtain ⟨a, ha, hsub, hcard, heq⟩ := hreduce (D ∩ Aᶜ) inter_subset_left t ht htcard
      have hneg := (hHom a).resolve_left ha.2
      simpa only [heq] using hneg (t.erase a) hsub hcard

/-- A countably complete diagonal ultrafilter has a large set homogeneous in
every finite dimension simultaneously. -/
theorem ultrafilter_finite_homogeneity (F : Ultrafilter Y)
    [CountableInterFilter (F : Filter Y)]
    (hdiag : ∀ A : Y → Set Y, (∀ a, A a ∈ F) →
      {y | ∀ a < y, y ∈ A a} ∈ F)
    (P : Finset Y → Prop) :
    ∃ S : Set Y, S ∈ F ∧ ∀ n : ℕ,
      (∀ t : Finset Y, (↑t : Set Y) ⊆ S → t.card = n → P t) ∨
      (∀ t : Finset Y, (↑t : Set Y) ⊆ S → t.card = n → ¬ P t) := by
  classical
  choose S hS hHom using fun n : ℕ => exists_homogeneous_card F hdiag n P
  let H : Set Y := ⋂ n, S n
  have hH : H ∈ F := countable_iInter_mem.mpr hS
  refine ⟨H, hH, ?_⟩
  intro n
  have hsub : H ⊆ S n := iInter_subset S n
  rcases hHom n with hp | hn
  · exact Or.inl (fun t ht hc => hp t (ht.trans hsub) hc)
  · exact Or.inr (fun t ht hc => hn t (ht.trans hsub) hc)

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_UltrafilterHomogeneity

section Gelfand465_part_Work_Gelfand465_Perfect_FiniteIntersectionCounting
open Set MeasureTheory
open scoped BigOperators

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {I : Type v} [MeasurableSpace X]

/-- Among 2n+1 measurable sets of probability at least one half, some n of
them have nonempty intersection. This is the finite counting contradiction
used after homogeneity in Fremlin451Q(c). -/
theorem exists_nonempty_intersection_of_half (μ : Measure X) [IsProbabilityMeasure μ]
    (K : I → Set X) (hKm : ∀ i, MeasurableSet (K i)) (T : Finset I) (n : ℕ)
    (hcard : T.card = 2 * n + 1) (hhalf : ∀ i ∈ T, (1 / 2 : ℝ) ≤ μ.real (K i)) :
    ∃ t : Finset I, t ⊆ T ∧ t.card = n ∧ (⋂ i ∈ t, K i).Nonempty := by
  classical
  by_contra hnone
  have hcount (x : X) : (T.filter fun i => x ∈ K i).card ≤ n := by
    by_contra hgt
    obtain ⟨t, htt, htcard⟩ := Finset.exists_subset_card_eq (le_of_lt (lt_of_not_ge hgt))
    apply hnone
    refine ⟨t, fun i hi => (Finset.mem_filter.mp (htt hi)).1, htcard, x, ?_⟩
    simp only [mem_iInter]
    intro i hi
    exact (Finset.mem_filter.mp (htt hi)).2
  let f : I → X → ℝ := fun i => (K i).indicator (fun _ => 1)
  have hfi (i : I) : Integrable (f i) μ := (integrable_const (1 : ℝ)).indicator (hKm i)
  have hbound (x : X) : ∑ i ∈ T, f i x ≤ (n : ℝ) := by
    have he : (∑ i ∈ T, f i x) = ((T.filter fun i => x ∈ K i).card : ℝ) := by
      simp only [f, indicator_apply, Finset.sum_boole]
    rw [he]
    exact_mod_cast hcount x
  have hupper : ∑ i ∈ T, μ.real (K i) ≤ (n : ℝ) := by
    calc
      (∑ i ∈ T, μ.real (K i)) = ∫ x, ∑ i ∈ T, f i x ∂μ := by
        rw [integral_finsetSum T (fun i _ => hfi i)]
        apply Finset.sum_congr rfl
        intro i _
        simp [f, integral_indicator_const, hKm i]
      _ ≤ ∫ _x : X, (n : ℝ) ∂μ :=
        integral_mono (integrable_finsetSum T (fun i _ => hfi i)) (integrable_const _) hbound
      _ = (n : ℝ) := by simp
  have hlower : ((2 * n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ≤ ∑ i ∈ T, μ.real (K i) := by
    calc
      ((2 * n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) = ∑ _i ∈ T, (1 / 2 : ℝ) := by
        simp [hcard, nsmul_eq_mul]
      _ ≤ ∑ i ∈ T, μ.real (K i) := Finset.sum_le_sum hhalf
  push_cast at hlower
  linarith

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_FiniteIntersectionCounting

section Gelfand465_part_Work_Gelfand465_Perfect_CompactHomogeneous
open Set MeasureTheory

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {I : Type v} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]

/-- Compactness and finite counting force a common point of a family which
is homogeneous in each finite dimension and whose members have mass at least
one half. No separation or Borel-source hypothesis is used. -/
theorem homogeneous_half_family_inter_nonempty (μ : Measure X) [IsProbabilityMeasure μ]
    (K : I → Set X) (hKm : ∀ i, MeasurableSet (K i)) (hKc : ∀ i, IsClosed (K i))
    (S : Set I) (hS : S.Infinite) (hhalf : ∀ i ∈ S, (1 / 2 : ℝ) ≤ μ.real (K i))
    (hhom : ∀ n : ℕ,
      (∀ t : Finset I, (↑t : Set I) ⊆ S → t.card = n → (⋂ i ∈ t, K i).Nonempty) ∨
      (∀ t : Finset I, (↑t : Set I) ⊆ S → t.card = n → ¬(⋂ i ∈ t, K i).Nonempty)) :
    (⋂ i ∈ S, K i).Nonempty := by
  classical
  have hpositive (n : ℕ) : ∀ t : Finset I, (↑t : Set I) ⊆ S → t.card = n →
      (⋂ i ∈ t, K i).Nonempty := by
    rcases hhom n with hp | hn
    · exact hp
    · obtain ⟨B, hBS, hBcard⟩ := hS.exists_subset_card_eq (2 * n + 1)
      obtain ⟨t, htB, htcard, htpos⟩ := exists_nonempty_intersection_of_half μ K hKm B n
        hBcard (fun i hi => hhalf i (hBS hi))
      exact False.elim (hn t (fun i hi => hBS (htB hi)) htcard htpos)
  have hfinite (T : Finset S) : (univ ∩ ⋂ i ∈ T, K i.val).Nonempty := by
    let t : Finset I := T.map (Function.Embedding.subtype S)
    have htS : (↑t : Set I) ⊆ S := by
      intro i hi
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
      exact a.property
    obtain ⟨x, hx⟩ := hpositive t.card t htS rfl
    refine ⟨x, mem_univ x, ?_⟩
    simp only [mem_iInter] at hx ⊢
    intro i hi
    exact hx i.val (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  obtain ⟨x, _, hx⟩ := isCompact_univ.inter_iInter_nonempty
    (fun i : S => K i.val) (fun i => hKc i.val) hfinite
  refine ⟨x, ?_⟩
  simp only [mem_iInter] at hx ⊢
  intro i hi
  exact hx ⟨i, hi⟩

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_CompactHomogeneous

section Gelfand465_part_Work_Gelfand465_Perfect_CompactUltrafilterObstruction
open Set Filter MeasureTheory
open scoped ENNReal

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]

/-- A compact inner-regular probability measure cannot realize a nonprincipal
countably complete ultrafilter as a measurable image. This is the actual
source-compactness contradiction of Fremlin451Q(c), keeping the index atom
separate from the source measure. -/
theorem no_diffuse_ultrafilter_representation (μ : Measure X) [IsProbabilityMeasure μ]
    (hreg : μ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet)
    (F : Ultrafilter Y) [CountableInterFilter (F : Filter Y)]
    (hdiffuse : ∀ y : Y, {y} ∉ F) (π : X → Y)
    (hpre : ∀ A : Set Y, MeasurableSet (π ⁻¹' A))
    (hlarge : ∀ A : Set Y, A ∈ F → μ (π ⁻¹' A) = 1) : False := by
  classical
  obtain ⟨ord, wf⟩ := exists_wellFoundedLT Y
  letI : LinearOrder Y := ord
  letI : WellFoundedLT Y := wf
  obtain ⟨g, hg, hpress⟩ := exists_pressingDown_image F (id : Y → Y) (by
    intro y
    simpa only [id_eq, setOf_eq_eq_singleton] using hdiffuse y)
  let G : Ultrafilter Y := F.map g
  letI : CountableInterFilter (G : Filter Y) := by
    change CountableInterFilter (Filter.map g (F : Filter Y))
    infer_instance
  have hGdiffuse (y : Y) : {y} ∉ G := by
    exact hg y
  have hdiag : ∀ A : Y → Set Y, (∀ a, A a ∈ G) → {y | ∀ a < y, y ∈ A a} ∈ G :=
    diagonal_mem_of_pressingDown G hpress
  obtain ⟨S, hS, htail⟩ := exists_large_tail_domain G hGdiffuse
  let π' : X → Y := g ∘ π
  have hpre' (A : Set Y) : MeasurableSet (π' ⁻¹' A) := hpre (g ⁻¹' A)
  have hlarge' (A : Set Y) (hA : A ∈ G) : μ (π' ⁻¹' A) = 1 :=
    hlarge (g ⁻¹' A) hA
  have hex (a : Y) : ∃ k : Set X, IsClosed k ∧ MeasurableSet k ∧
      (a ∈ S → k ⊆ π' ⁻¹' (S ∩ Ioi a) ∧ (1 / 2 : ℝ) ≤ μ.real k) := by
    by_cases ha : a ∈ S
    · have hmass : μ (π' ⁻¹' (S ∩ Ioi a)) = 1 := hlarge' _ (inter_mem hS (htail a ha))
      obtain ⟨k, hk, ⟨hkc, hkm⟩, hhalf⟩ := hreg (hpre' (S ∩ Ioi a))
        (ENNReal.ofReal (1 / 2 : ℝ)) (by rw [hmass]; norm_num)
      refine ⟨k, hkc, hkm, fun _ => ⟨hk, ?_⟩⟩
      exact ((ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) (measure_ne_top μ k)).mp hhalf).le
    · exact ⟨∅, isClosed_empty, MeasurableSet.empty, fun h => (ha h).elim⟩
  choose K hKc hKm hKs using hex
  obtain ⟨H, hH, hhom⟩ := ultrafilter_finite_homogeneity G hdiag
    (fun t : Finset Y => (⋂ i ∈ t, K i).Nonempty)
  let T : Set Y := S ∩ H
  have hT : T ∈ G := inter_mem hS hH
  have hTinf : T.Infinite := by
    intro hfin
    obtain ⟨y, _, he⟩ := Ultrafilter.eq_pure_of_finite_mem hfin hT
    apply hGdiffuse y
    rw [he]
    exact Ultrafilter.mem_pure.mpr rfl
  have hThom : ∀ n : ℕ,
      (∀ t : Finset Y, (↑t : Set Y) ⊆ T → t.card = n → (⋂ i ∈ t, K i).Nonempty) ∨
      (∀ t : Finset Y, (↑t : Set Y) ⊆ T → t.card = n → ¬(⋂ i ∈ t, K i).Nonempty) := by
    intro n
    rcases hhom n with hp | hn
    · exact Or.inl (fun t ht hc => hp t (ht.trans inter_subset_right) hc)
    · exact Or.inr (fun t ht hc => hn t (ht.trans inter_subset_right) hc)
  obtain ⟨x, hx⟩ := homogeneous_half_family_inter_nonempty μ K hKm hKc T hTinf
    (fun i hi => (hKs i hi.1).2) hThom
  have hxK : ∀ i ∈ T, x ∈ K i := by simpa only [mem_iInter] using hx
  obtain ⟨a₀, ha₀⟩ := G.nonempty_of_mem hT
  have hxS : π' x ∈ S := ((hKs a₀ ha₀.1).1 (hxK a₀ ha₀)).1
  obtain ⟨a, haT, hax⟩ := G.nonempty_of_mem (inter_mem hT (htail (π' x) hxS))
  have hxa : a < π' x := ((hKs a haT.1).1 (hxK a haT)).2
  exact (lt_asymm hxa hax)

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_CompactUltrafilterObstruction

section Gelfand465_part_Work_Gelfand465_Perfect_FiniteNullFamily
open Set Filter MeasureTheory
open scoped ENNReal

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {Y : Type v} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]

/-- The finite null-partition conclusion of Fremlin451Q. If every union of
fibres is measurable in a compact inner-regular finite measure space, and each
fibre is null, then the whole measure is zero. Both the genuinely atomless and
nonprincipal-index-atom branches are included. -/
theorem eq_zero_of_all_preimages_measurable_null_fibres (μ : Measure X) [IsFiniteMeasure μ]
    (hreg : μ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet)
    (π : X → Y) (hpre : ∀ A : Set Y, MeasurableSet (π ⁻¹' A))
    (hfibres : ∀ y : Y, μ (π ⁻¹' {y}) = 0) : μ = 0 := by
  classical
  by_contra hne
  letI : MeasurableSpace Y := ⊤
  have hall : ∀ A : Set Y, MeasurableSet A := fun _ => trivial
  have hπ : Measurable π := fun A _ => hpre A
  let ν : Measure Y := μ.map π
  have hνne : ν ≠ 0 := (Measure.map_ne_zero_iff hπ.aemeasurable).mpr hne
  letI : NullSingletonClass ν := ⟨fun y => by
    rw [Measure.map_apply hπ (hall {y})]
    exact hfibres y⟩
  have hperfect : HasPerfectRealImages μ := by
    intro f hf E hE hpos
    exact exists_compact_positive_image μ hreg f hf hE hpos
  have hnot := not_splitting_perfect_powerset ν hνne (hperfect.map π hπ) hall
  obtain ⟨A, hA⟩ := exists_positiveMeasureAtom_of_not_splitting ν hnot
  let μA : Measure X := μ.restrict (π ⁻¹' A)
  have hmass : 0 < μ (π ⁻¹' A) := by
    simpa only [ν, Measure.map_apply hπ (hall A)] using hA.2.1
  letI : NeZero μA := ⟨fun hz => hmass.ne' (Measure.restrict_eq_zero.mp hz)⟩
  let c : ℝ≥0∞ := (μA univ)⁻¹
  let ρ : Measure X := c • μA
  letI : IsProbabilityMeasure ρ := inferInstance
  have hregA : μA.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet :=
    Measure.InnerRegularWRT.restrict_of_measure_ne_top
      (fun _ hU r hr => hreg hU.1 r hr) (measure_ne_top μ _)
  have hregρ : ρ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet :=
    hregA.smul c
  let F : Ultrafilter Y := hA.ultrafilter hall
  letI : CountableInterFilter (F : Filter Y) := inferInstance
  have hFdiffuse (y : Y) : {y} ∉ F := by
    intro hy
    have he : F = pure y := Ultrafilter.eq_of_le (Filter.le_pure_iff.mpr hy)
    exact hA.ultrafilter_ne_pure hall y he
  have hmap : μA.map π = ν.restrict A := (Measure.restrict_map hπ (hall A)).symm
  apply no_diffuse_ultrafilter_representation ρ hregρ F hFdiffuse π hpre
  intro B hB
  apply (prob_compl_eq_zero_iff (μ := ρ) (hpre B)).mp
  have hz : μA (π ⁻¹' Bᶜ) = 0 := by
    rw [← Measure.map_apply hπ (hall Bᶜ), hmap]
    exact hB
  change (c • μA) (π ⁻¹' B)ᶜ = 0
  rw [← preimage_compl, Measure.smul_apply, hz, smul_zero]

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_FiniteNullFamily

section Gelfand465_part_Work_Gelfand465_Perfect_NullFamilies
open Set MeasureTheory

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {I : Type v}

/-- The index of a disjoint-family member, with `none` outside its union. -/
noncomputable def familyIndex (r : I → Set X) (x : X) : Option I := by
  classical
  exact if h : ∃ i, x ∈ r i then some h.choose else none

theorem familyIndex_eq_some_iff (r : I → Set X) (hd : Pairwise (Function.onFun Disjoint r))
    (x : X) (i : I) : familyIndex r x = some i ↔ x ∈ r i := by
  classical
  unfold familyIndex
  split_ifs with h
  · have huniq : ∀ j, x ∈ r j → h.choose = j := by
      intro j hj
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) h.choose_spec hj
    constructor
    · intro he
      have hi := Option.some.inj he
      exact hi ▸ h.choose_spec
    · intro hi
      exact congrArg some (huniq i hi)
  · constructor
    · intro he
      cases he
    · intro hi
      exact False.elim (h ⟨i, hi⟩)

theorem familyIndex_eq_none_iff (r : I → Set X) (x : X) :
    familyIndex r x = none ↔ x ∉ ⋃ i, r i := by
  classical
  unfold familyIndex
  split_ifs with h
  · constructor
    · intro he
      cases he
    · intro hn
      exact False.elim (hn (mem_iUnion.mpr h))
  · constructor
    · intro _ hx
      exact h (mem_iUnion.mp hx)
    · intro _
      rfl

theorem familyIndex_preimage (r : I → Set X) (hd : Pairwise (Function.onFun Disjoint r)) (A : Set (Option I)) :
    familyIndex r ⁻¹' A =
      {x | none ∈ A ∧ x ∉ ⋃ i, r i} ∪ ⋃ i ∈ {i | some i ∈ A}, r i := by
  classical
  ext x
  constructor
  · intro hx
    change familyIndex r x ∈ A at hx
    cases he : familyIndex r x with
    | none =>
      left
      refine ⟨?_, (familyIndex_eq_none_iff r x).mp he⟩
      rwa [he] at hx
    | some i =>
      right
      have hiA : some i ∈ A := by rwa [he] at hx
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiA, (familyIndex_eq_some_iff r hd x i).mp he⟩⟩
  · rintro (hx | hx)
    · change familyIndex r x ∈ A
      rw [(familyIndex_eq_none_iff r x).mpr hx.2]
      exact hx.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨hiA, hxi⟩ := mem_iUnion.mp hi
      change familyIndex r x ∈ A
      rw [(familyIndex_eq_some_iff r hd x i).mpr hxi]
      exact hiA

/-- The disjoint-null-family formulation of the finite compact-measure theorem. -/
theorem measure_iUnion_eq_zero_of_all_subunions_measurable
    [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (hreg : μ.InnerRegularWRT (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet)
    (r : I → Set X) (hd : Pairwise (Function.onFun Disjoint r))
    (hsub : ∀ J : Set I, MeasurableSet (⋃ i ∈ J, r i))
    (hnull : ∀ i, μ (r i) = 0) : μ (⋃ i, r i) = 0 := by
  classical
  have hU : MeasurableSet (⋃ i, r i) := by simpa only [biUnion_univ] using hsub univ
  have hpre (A : Set (Option I)) : MeasurableSet (familyIndex r ⁻¹' A) := by
    rw [familyIndex_preimage r hd A]
    apply MeasurableSet.union _ (hsub _)
    by_cases hn : none ∈ A
    · have he : {x : X | none ∈ A ∧ x ∉ ⋃ i, r i} = (⋃ i, r i)ᶜ := by
        ext x
        simp only [mem_setOf_eq, mem_compl_iff, hn, true_and]
      rw [he]
      exact hU.compl
    · simp only [hn, false_and, setOf_false]
      exact MeasurableSet.empty
  have hreg' : (μ.restrict (⋃ i, r i)).InnerRegularWRT
      (fun k => IsClosed k ∧ MeasurableSet k) MeasurableSet :=
    Measure.InnerRegularWRT.restrict_of_measure_ne_top
      (fun _ hU r hr => hreg hU.1 r hr) (measure_ne_top μ _)
  apply Measure.restrict_eq_zero.mp
  apply eq_zero_of_all_preimages_measurable_null_fibres _ hreg' (familyIndex r) hpre
  intro i
  rw [Measure.restrict_apply (hpre {i})]
  cases i with
  | none =>
    have he : familyIndex r ⁻¹' {none} = (⋃ i, r i)ᶜ := by
      ext x
      exact familyIndex_eq_none_iff r x
    rw [he, compl_inter_self, measure_empty]
  | some i =>
    have he : familyIndex r ⁻¹' {some i} = r i := by
      ext x
      exact familyIndex_eq_some_iff r hd x i
    rw [he]
    exact measure_mono_null inter_subset_left (hnull i)

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_NullFamilies

section Gelfand465_part_Work_Gelfand465_Perfect_EnhancedNullFamilies
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality

namespace Gelfand465Perfect
universe u v
variable {X : Type u} {I : Type v}

/-- Fremlin451Q in precisely the enhanced-space form required by the current
Proposition4.65: compactness and the canonical faithful semifinite complex measure
force every measurable-all-subunions disjoint family of negligible sets to have
negligible union. -/
theorem negligible_iUnion_of_compact_semifinite (E : Enhanced X)
    (hc : IsCompactEnhancedOn E univ)
    (hμ : ∃ (M' : Set (Set X)) (μ : Set X → ℂ),
      IsEMeasure E M' μ ∧ IsFaithfulEMeasure E M' μ ∧ IsSemifiniteEMeasure E M')
    (r : I → Set X) (hd : Pairwise (Function.onFun Disjoint r))
    (hsub : ∀ J : Set I, (⋃ i ∈ J, r i) ∈ E.measurable)
    (hnull : ∀ i, r i ∈ E.negligible) : (⋃ i, r i) ∈ E.negligible := by
  classical
  letI := Gelfand454.measurableSpace E
  obtain ⟨M', μ, hmeasure, hfaithful, hsemifinite⟩ := hμ
  have hU : (⋃ i, r i) ∈ E.measurable := by simpa only [biUnion_univ] using hsub univ
  by_contra hnon
  obtain ⟨m, hm, hmn, hmU⟩ := hsemifinite _ hU hnon
  let μm : Set X → ℂ := fun s => μ (s ∩ m)
  let hμm : IsEMeasure E E.measurable μm := isEMeasure_inter E M' μ hmeasure m hm
  let ν := Gelfand454.finiteMeasure E μm hμm
  have hνnull (s : Set X) (hs : s ∈ E.measurable) :
      ν s = 0 ↔ s ∩ m ∈ E.negligible :=
    finiteMeasure_inter_null_iff_measurable E M' μ hmeasure hfaithful m hm hs
  obtain ⟨t, ht, hreg⟩ := compactEnhanced_innerRegular_relative E hc m (hmeasure.1 hm) ν hνnull
  letI : TopologicalSpace X := t
  letI : CompactSpace X := ht
  have hνzero : ν (⋃ i, r i) = 0 :=
    measure_iUnion_eq_zero_of_all_subunions_measurable ν hreg r hd hsub (fun i =>
      (hνnull (r i) (E.negligibleMeasurable (hnull i))).mpr
        (negligible_mono E inter_subset_left (hnull i)))
  have hn := (hνnull _ hU).mp hνzero
  rw [inter_eq_right.mpr hmU] at hn
  exact hmn hn

end Gelfand465Perfect
end Gelfand465_part_Work_Gelfand465_Perfect_EnhancedNullFamilies

section Gelfand465_part_Work_Gelfand465_Final
open Set GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20

namespace Gelfand465Assembly
universe u

/-- The exact current Proposition4.65, assembled from canonical finite
restrictions, the proved compact null-family theorem, component kernel maxima,
and actual strictly-localizing inverse premaps. -/
theorem proposition_4_65_proof {X X' : Type u} (E : Enhanced X) (E' : Enhanced X')
    (hc : IsCompactEnhancedOn E Set.univ)
    (hμ : ∃ (M' : Set (Set X)) (μ : Set X → ℂ),
      IsEMeasure E M' μ ∧ IsFaithfulEMeasure E M' μ ∧ IsSemifiniteEMeasure E M')
    (hsl : IsStrictlyLocalizable E') (f : Premap E E') :
    (∃ m : Set X', IsMeasurableImage E E' f m) ∧
    ∀ m₀ m₁ : Set X', IsMeasurableImage E E' f m₀ → IsMeasurableImage E E' f m₁ →
      (m₀ \ m₁) ∪ (m₁ \ m₀) ∈ E'.negligible := by
  obtain ⟨I, Y, F, hF, a, b, hleft, _⟩ := hsl
  obtain ⟨p, hpm, hpn, hmax⟩ := exists_kernelMaximum_coprod E F hF (compPremap f a)
    (fun r hd hsub hn => Gelfand465Perfect.negligible_iUnion_of_compact_semifinite
      E hc hμ r hd hsub hn)
  have hp := kernelMaximum_transport E E' (coprodEnhanced F) f a b hleft p hpm hpn hmax
  refine ⟨⟨(partialPreimage a.val p)ᶜ, ?_⟩, ?_⟩
  · exact (Gelfand465.measurableImage_compl_iff E E' f (partialPreimage a.val p)).mpr hp
  · intro m₀ m₁ h₀ h₁
    exact Gelfand465.measurableImage_unique E E' f h₀ h₁

end Gelfand465Assembly
end Gelfand465_part_Work_Gelfand465_Final

open GelfandVNA.Duality QAlgorithms.Papers.Independent.Support21.P20
universe u
theorem solution {X X' : Type u} (E : Enhanced X) (E' : Enhanced X')
    (hc : IsCompactEnhancedOn E Set.univ)
    (hμ : ∃ (M' : Set (Set X)) (μ : Set X → ℂ),
      IsEMeasure E M' μ ∧ IsFaithfulEMeasure E M' μ ∧ IsSemifiniteEMeasure E M')
    (hsl : IsStrictlyLocalizable E') (f : Premap E E') :
    (∃ m : Set X', IsMeasurableImage E E' f m) ∧
    ∀ m₀ m₁ : Set X', IsMeasurableImage E E' f m₀ → IsMeasurableImage E E' f m₁ →
      (m₀ \ m₁) ∪ (m₁ \ m₀) ∈ E'.negligible := by
  exact Gelfand465Assembly.proposition_4_65_proof E E' hc hμ hsl f
