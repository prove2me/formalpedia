-- Prove2me | solution 1 for GelfandVNA.Duality.proposition_4_54
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:14:54.207202+00:00
-- url     : https://prove2.me/submissions/bb078bfd-c033-4650-86df-f2918bf178a2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_EMS

/-!
Direct proof of Pavlov's Proposition 4.54, with unchanged canonical definitions.
The localizability criterion reuses fizzyinc3's accepted proof,
submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f, with a namespace/name wrapper.
All remaining construction and measure proofs are included below.
-/
noncomputable section

section Gelfand454_part_FiniteMeasure
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
end Gelfand454_part_FiniteMeasure

section Gelfand454_part_CountableSup
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
end Gelfand454_part_CountableSup

section Gelfand454_part_CompleteOrder
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
end Gelfand454_part_CompleteOrder

section Gelfand454_part_BooleanAlgebra
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
end Gelfand454_part_BooleanAlgebra

section Gelfand454_part_QuotientMeasure
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open scoped NNReal ENNReal

namespace Gelfand454
universe u
variable {X : Type u} (E : Enhanced X)
variable (ν : @Measure X (measurableSpace E)) [IsFiniteMeasure ν]
variable (hnull : ∀ s : Set X, ν s = 0 ↔ s ∈ E.negligible)

/-- The finite positive measure descends to the canonical quotient. -/
noncomputable def quotientMeasure : MmodN E → ℝ≥0 := by
  letI := measurableSpace E
  refine Quotient.lift (fun s => (ν s.1).toNNReal) ?_
  intro a b h
  apply congrArg ENNReal.toNNReal
  apply measure_congr
  apply ae_eq_set.2
  exact ⟨(hnull _).2 (negligible_mono E Set.subset_union_left h),
    (hnull _).2 (negligible_mono E Set.subset_union_right h)⟩

theorem quotientMeasure_mk {s : Set X} (hs : s ∈ E.measurable) :
    quotientMeasure E ν hnull (MmodN.mk s hs) = (ν s).toNNReal := rfl

theorem coe_quotientMeasure (a : MmodN E) :
    (quotientMeasure E ν hnull a : ℝ≥0∞) = ν a.out.1 := by
  have h := congrArg (fun q => (quotientMeasure E ν hnull q : ℝ≥0∞)) (mk_out E a)
  rw [quotientMeasure_mk, ENNReal.coe_toNNReal (measure_ne_top _ _)] at h
  exact h.symm

theorem quotientMeasure_mono : Monotone (quotientMeasure E ν hnull) := by
  letI := measurableSpace E
  intro a b hab
  induction a using Quotient.ind with
  | _ a =>
    induction b using Quotient.ind with
    | _ b =>
      apply ENNReal.toNNReal_mono (measure_ne_top _ _)
      exact measure_mono_ae (ae_le_set.2 ((hnull _).2 hab))

theorem quotientMeasure_zero_iff (a : MmodN E) :
    quotientMeasure E ν hnull a = 0 ↔ a = MmodN.mk ∅ E.sigmaAlgebra.1 := by
  letI := measurableSpace E
  induction a using Quotient.ind with
  | _ a =>
    change (ν a.1).toNNReal = 0 ↔ MmodN.mk a.1 a.2 = MmodN.mk ∅ E.sigmaAlgebra.1
    constructor
    · intro h
      have hz : ν a.1 = 0 := by
        rw [← ENNReal.coe_toNNReal (measure_ne_top ν a.1), h, ENNReal.coe_zero]
      apply Quotient.sound
      change (a.1 \ ∅) ∪ (∅ \ a.1) ∈ E.negligible
      simpa only [Set.sdiff_empty, Set.empty_sdiff, Set.union_empty] using (hnull _).1 hz
    · intro h
      have hn := Quotient.exact h
      change (a.1 \ ∅) ∪ (∅ \ a.1) ∈ E.negligible at hn
      have hz : ν a.1 = 0 := (hnull _).2 (by
        simpa only [Set.sdiff_empty, Set.empty_sdiff, Set.union_empty] using hn)
      simp only [hz, ENNReal.toNNReal_zero]

end Gelfand454
end Gelfand454_part_QuotientMeasure

section Gelfand454_part_DirectedContinuity
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open scoped NNReal ENNReal

namespace Gelfand454
universe u
variable {X : Type u} (E : Enhanced X)
variable (ν : @Measure X (measurableSpace E)) [IsFiniteMeasure ν]
variable (hnull : ∀ s : Set X, ν s = 0 ↔ s ∈ E.negligible)

/-- The quotient valuation preserves every existing directed supremum. The
argument uses a countable essential union and continuity from below of ν. -/
theorem quotientMeasure_preservesDirectedSuprema :
    PreservesDirectedSuprema (quotientMeasure E ν hnull) := by
  classical
  letI := measurableSpace E
  intro S a hne hdir hLUB
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact quotientMeasure_mono E ν hnull (hLUB.1 hb)
  · intro x hx
    let C : Set (Set X) := (fun q : MmodN E => q.out.1) '' S
    have hC : ∀ s ∈ C, MeasurableSet s := by
      rintro s ⟨q, hq, rfl⟩
      exact q.out.2
    obtain ⟨D, hDC, hDc, hD⟩ := ν.exists_ae_subset_biUnion_countable hC
    have hDm : MeasurableSet (⋃₀ D) := MeasurableSet.sUnion hDc (fun s hs => hC s (hDC hs))
    have hDmem : (⋃₀ D) ∈ E.measurable := hDm
    have hqLUB : IsLUB S (MmodN.mk (⋃₀ D) hDmem) := by
      constructor
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
    rw [← hqLUB.unique hLUB]
    change (ν (⋃₀ D)).toNNReal ≤ x
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal (measure_ne_top _ _)]
    rcases D.eq_empty_or_nonempty with rfl | hDne
    · simp
    obtain ⟨r, hr⟩ := hDc.exists_eq_range hDne
    have hrC (i : ℕ) : r i ∈ C := hDC (by rw [hr]; exact Set.mem_range_self i)
    have hrm (i : ℕ) : r i ∈ E.measurable := hC _ (hrC i)
    choose b hb hbr using hrC
    rw [hr, Set.sUnion_range, measure_iUnion_eq_iSup_accumulate]
    apply iSup_le
    intro n
    letI : Nonempty S := hne.to_subtype
    obtain ⟨z, hz⟩ := hdir.directed_val.finite_le
      (fun i : Fin (n + 1) => (⟨b i, hb i⟩ : S))
    have hsub : accumulate r n ≤ᵐ[ν] z.1.out.1 := by
      apply ae_le_set.2
      rw [Set.accumulate_def]
      simp_rw [Set.iUnion_sdiff]
      apply (measure_biUnion_null_iff (Set.to_countable (Set.Iic n))).2
      intro i hi
      apply (hnull _).2
      have h : MmodN.mk (r i) (hrm i) ≤ z.1 := by
        have he : (⟨r i, hrm i⟩ : {s : Set X // s ∈ E.measurable}) = (b i).out :=
          Subtype.ext (hbr i).symm
        calc
          MmodN.mk (r i) (hrm i) = MmodN.mk (b i).out.1 (b i).out.2 :=
            congrArg (fun s : {s : Set X // s ∈ E.measurable} =>
              MmodN.mk s.1 s.2) he
          _ = b i := mk_out E _
          _ ≤ z.1 := hz ⟨i, Nat.lt_succ_iff.mpr hi⟩
      rwa [← mk_out E z.1] at h
    calc
      ν (accumulate r n) ≤ ν z.1.out.1 := measure_mono_ae hsub
      _ = (quotientMeasure E ν hnull z.1 : ℝ≥0∞) := (coe_quotientMeasure E ν hnull z.1).symm
      _ ≤ (x : ℝ≥0∞) := ENNReal.coe_le_coe.mpr
        (hx (Set.mem_image_of_mem (quotientMeasure E ν hnull) z.2))

end Gelfand454
end Gelfand454_part_DirectedContinuity

section Gelfand454_part_LocalizableCriterion
/- Reused accepted proof by fizzyinc3, submission e4ac8c1d-3289-4144-baeb-8ddb71a3176f. Only a wrapper namespace and theorem name change. -/

namespace Gelfand273Criterion

open QAlgorithms.Papers.Independent.Support21.P20

open Set Filter

open scoped NNReal

universe u v

theorem g67c_restrict {A : Type u} [CompleteBooleanAlgebra A] (nu : A → ℝ≥0)
    (hnu : IsPositiveContinuousValuation nu) (a : A) :
    IsPositiveContinuousValuation (fun x : Set.Iic a => nu x.val) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu
  refine ⟨⟨hbot, fun x y => hmod x.val y.val⟩, fun x y hxy => hmono hxy, ?_⟩
  intro s b hsne hdir hlub
  have hl : IsLUB (Subtype.val '' s) b.val := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩; exact hlub.1 hx
    · intro u hu
      have : b ≤ ⟨u ⊓ a, inf_le_right⟩ := hlub.2 (fun x hx =>
        show x.val ≤ u ⊓ a from le_inf (hu ⟨x, hx, rfl⟩) x.2)
      exact (show b.val ≤ u ⊓ a from this).trans inf_le_left
  have hd : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
    exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩
  have h := hcont _ _ (hsne.image _) hd hl
  rw [Set.image_image] at h
  exact h

theorem g67c_extend {A : Type u} [CompleteBooleanAlgebra A] (a : A) (mu : Set.Iic a → ℝ≥0)
    (hmu : IsPositiveContinuousValuation mu) :
    IsPositiveContinuousValuation (fun x : A => mu ⟨x ⊓ a, inf_le_right⟩) := by
  obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hmu
  refine ⟨⟨?_, fun x y => ?_⟩, fun x y hxy => hmono (show x ⊓ a ≤ y ⊓ a from inf_le_inf_right a hxy), ?_⟩
  · have : (⟨(⊥ : A) ⊓ a, inf_le_right⟩ : Set.Iic a) = ⊥ := Subtype.ext (by simp)
    simp only; rw [this, hbot]
  · have h1 : (⟨(x ⊔ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊔ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊔ y) ⊓ a = (x ⊓ a) ⊔ (y ⊓ a)
        rw [inf_sup_right])
    have h2 : (⟨(x ⊓ y) ⊓ a, inf_le_right⟩ : Set.Iic a) =
        (⟨x ⊓ a, inf_le_right⟩ : Set.Iic a) ⊓ ⟨y ⊓ a, inf_le_right⟩ :=
      Subtype.ext (by
        show (x ⊓ y) ⊓ a = (x ⊓ a) ⊓ (y ⊓ a)
        rw [inf_inf_distrib_right])
    simp only; rw [h1, h2]; exact hmod _ _
  · intro s b hsne hdir hlub
    let g : A → Set.Iic a := fun x => ⟨x ⊓ a, inf_le_right⟩
    have hb : b = sSup s := hlub.unique (isLUB_sSup s)
    have hl : IsLUB (g '' s) (g b) := by
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact show x ⊓ a ≤ b ⊓ a from inf_le_inf_right a (hlub.1 hx)
      · intro u hu
        show b ⊓ a ≤ u.val
        rw [hb, sSup_inf_eq]
        exact iSup₂_le fun x hx => (show g x ≤ u from hu ⟨x, hx, rfl⟩)
    have hd : DirectedOn (· ≤ ·) (g '' s) := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hxz, hyz⟩ := hdir x hx y hy
      exact ⟨g z, ⟨z, hz, rfl⟩, show x ⊓ a ≤ z ⊓ a from inf_le_inf_right a hxz,
        show y ⊓ a ≤ z ⊓ a from inf_le_inf_right a hyz⟩
    have h := hcont _ _ (hsne.image _) hd hl
    rw [Set.image_image] at h
    exact h

theorem localizableCriterion (A : Type u) [CompleteBooleanAlgebra A] :
    HasFiniteValuationCover A ↔ ∀ b : A, b ≠ ⊥ →
      ∃ nu : A → ℝ≥0, IsPositiveContinuousValuation nu ∧ nu b ≠ 0 := by
  constructor
  · intro hcov b hb
    have : ∃ g ∈ {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}, b ⊓ g ≠ ⊥ := by
      by_contra hall
      push Not at hall
      apply hb
      have : b = b ⊓ ⊤ := (inf_top_eq b).symm
      rw [this, ← hcov, inf_sSup_eq]
      exact le_antisymm (iSup₂_le fun d hd => (hall d hd).le) bot_le
    obtain ⟨g, ⟨mu, hmu, hfaith⟩, hbg⟩ := this
    refine ⟨_, g67c_extend g mu hmu, fun h0 => hbg ?_⟩
    have := hfaith _ h0
    exact congrArg Subtype.val this
  · intro h
    unfold HasFiniteValuationCover
    set G := {a : A | ∃ nu : Set.Iic a → ℝ≥0,
        IsPositiveContinuousValuation nu ∧ ∀ b, nu b = 0 → b = ⊥}
    set g := sSup G
    by_contra hne
    have hgc : gᶜ ≠ ⊥ := fun h' => hne (compl_eq_bot.1 h')
    obtain ⟨nu, hnu, hnz⟩ := h gᶜ hgc
    have hnu' := hnu
    obtain ⟨⟨hbot, hmod⟩, hmono, hcont⟩ := hnu'
    let Z : Set A := {x | nu x = 0}
    set n := sSup Z
    have hsupz : ∀ x y, x ∈ Z → y ∈ Z → x ⊔ y ∈ Z := by
      intro x y hx hy
      have := hmod x y
      simp only [Z, Set.mem_setOf_eq] at hx hy ⊢
      rw [hx, hy, zero_add] at this
      exact (add_eq_zero.1 this.symm).1
    have hn : nu n = 0 := by
      have hc := hcont Z n ⟨⊥, hbot⟩
        (fun x hx y hy => ⟨x ⊔ y, hsupz x y hx hy, le_sup_left, le_sup_right⟩) (isLUB_sSup Z)
      exact le_antisymm (hc.2 (by rintro _ ⟨x, hx, rfl⟩; exact le_of_eq hx)) bot_le
    set c := gᶜ ⊓ nᶜ
    have hcG : c ∈ G := by
      refine ⟨fun x => nu x.val, g67c_restrict nu hnu c, fun x hx => ?_⟩
      apply Subtype.ext
      have hxn : x.val ≤ n := le_sSup hx
      have hxc : x.val ≤ nᶜ := x.2.trans inf_le_right
      show x.val = ⊥
      exact le_antisymm (le_inf hxn hxc |>.trans (inf_compl_self n).le) bot_le
    have hcle : c ≤ g := le_sSup hcG
    have hc0 : c = ⊥ := le_antisymm ((le_inf hcle inf_le_left).trans (inf_compl_self g).le) bot_le
    apply hnz
    have h1 : gᶜ ≤ c ⊔ n := by
      rw [sup_comm, sup_inf_left, sup_compl_eq_top, inf_top_eq]; exact le_sup_right
    have h2 := hmono h1
    rw [hc0, bot_sup_eq, hn] at h2
    exact le_antisymm h2 bot_le

end Gelfand273Criterion
end Gelfand454_part_LocalizableCriterion

section Gelfand454_part_ProductCover
open Set QAlgorithms.Papers.Independent.Support21.P20
open scoped NNReal

namespace Gelfand454
universe u v

theorem valuation_eval {I : Type u} {B : I → Type v}
    [∀ i, CompleteBooleanAlgebra (B i)] (i : I) (ν : B i → ℝ≥0)
    (hν : IsPositiveContinuousValuation ν) :
    IsPositiveContinuousValuation (fun b : ∀ j, B j => ν (b i)) := by
  refine ⟨⟨hν.1.1, fun a b => hν.1.2 (a i) (b i)⟩,
    fun a b hab => hν.2.1 (hab i), ?_⟩
  intro S a hne hdir hLUB
  have hdi : DirectedOn (· ≤ ·) ((fun b : ∀ j, B j => b i) '' S) := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    obtain ⟨d, hd, hbd, hcd⟩ := hdir b hb c hc
    exact ⟨d i, ⟨d, hd, rfl⟩, hbd i, hcd i⟩
  have h := hν.2.2 _ _ (hne.image _) hdi (isLUB_pi.mp hLUB i)
  simpa only [Set.image_image] using h

/-- Products of Boolean algebras carrying faithful finite continuous
valuations are localizable; coordinate valuations separate nonzero elements. -/
theorem product_hasFiniteValuationCover {I : Type u} {B : I → Type v}
    [∀ i, CompleteBooleanAlgebra (B i)]
    (ν : ∀ i, B i → ℝ≥0) (hν : ∀ i, IsPositiveContinuousValuation (ν i))
    (hf : ∀ i b, ν i b = 0 → b = ⊥) : HasFiniteValuationCover (∀ i, B i) := by
  apply (Gelfand273Criterion.localizableCriterion _).2
  intro b hb
  have hi : ∃ i, b i ≠ ⊥ := by
    by_contra h
    push_neg at h
    apply hb
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hi
  exact ⟨fun b => ν i (b i), valuation_eval i (ν i) (hν i), fun h => hi (hf i (b i) h)⟩

end Gelfand454
end Gelfand454_part_ProductCover

section Gelfand454_part_SigmaFiniteValuation
open Set MeasureTheory QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open scoped NNReal ENNReal

namespace Gelfand454
universe u
variable {X : Type u} (E : Enhanced X) (hE : IsSigmaFiniteE E)

/-- The descended finite measure satisfies the modular valuation identity. -/
theorem quotientMeasure_isValuation
    (ν : @Measure X (measurableSpace E)) [IsFiniteMeasure ν]
    (hnull : ∀ s : Set X, ν s = 0 ↔ s ∈ E.negligible) :
    letI := quotientCompleteBooleanAlgebra E hE
    IsValuation (quotientMeasure E ν hnull) := by
  letI := measurableSpace E
  letI := quotientCompleteBooleanAlgebra E hE
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
  constructor
  · rw [← hBot, quotientMeasure_mk]
    simp only [measure_empty, ENNReal.toNNReal_zero]
  · intro a b
    induction a using Quotient.ind with
    | _ a =>
      induction b using Quotient.ind with
      | _ b =>
        change quotientMeasure E ν hnull (MmodN.mk a.1 a.2) +
          quotientMeasure E ν hnull (MmodN.mk b.1 b.2) =
          quotientMeasure E ν hnull (MmodN.mk a.1 a.2 ⊔ MmodN.mk b.1 b.2) +
          quotientMeasure E ν hnull (MmodN.mk a.1 a.2 ⊓ MmodN.mk b.1 b.2)
        rw [← hSup, ← hInf]
        simp only [quotientMeasure_mk]
        apply ENNReal.coe_injective
        simpa only [ENNReal.coe_add, ENNReal.coe_toNNReal (measure_ne_top ν _)] using
          (measure_union_add_inter a.1 (show MeasurableSet b.1 from b.2)).symm

/-- A sigma-finite enhanced space has a faithful positive continuous valuation
on its exact complete Boolean quotient. -/
theorem sigmaFinite_faithfulValuation :
    letI := quotientCompleteBooleanAlgebra E hE
    ∃ ρ : MmodN E → ℝ≥0,
      IsPositiveContinuousValuation ρ ∧ ∀ a, ρ a = 0 → a = ⊥ := by
  letI := measurableSpace E
  letI := quotientCompleteBooleanAlgebra E hE
  obtain ⟨ν, hν, hnull⟩ := exists_finiteMeasure E hE
  letI := hν
  refine ⟨quotientMeasure E ν hnull,
    ⟨quotientMeasure_isValuation E hE ν hnull,
      quotientMeasure_mono E ν hnull,
      quotientMeasure_preservesDirectedSuprema E ν hnull⟩, ?_⟩
  intro a ha
  have he := (quotientMeasure_zero_iff E ν hnull a).1 ha
  apply le_antisymm _ bot_le
  rw [he]
  generalize hq : (⊥ : MmodN E) = q
  induction q using Quotient.ind with
  | _ b => exact mk_mono E _ b.2 (Set.empty_subset _)

end Gelfand454
end Gelfand454_part_SigmaFiniteValuation

section Gelfand454_part_CoprodIso
set_option autoImplicit false
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
end Gelfand454_part_CoprodIso

section Gelfand454_part_Final
open QAlgorithms.Papers.Independent.Support21.P20 GelfandVNA.Duality
open Gelfand454 Gelfand454Coprod
open scoped NNReal
universe u

theorem solution {X : Type u} (E : Enhanced X) (hE : IsStrictlyLocalizable E) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B),
      HasFiniteValuationCover B ∧ Nonempty (MmodN E ≃o B) := by
  classical
  obtain ⟨I, Y, F, hF, f, g, hgf, hfg⟩ := hE
  letI (i : I) : CompleteBooleanAlgebra (MmodN (F i)) :=
    quotientCompleteBooleanAlgebra (F i) (hF i)
  have H (i : I) : ∃ ρ : MmodN (F i) → ℝ≥0,
      IsPositiveContinuousValuation ρ ∧ ∀ a, ρ a = 0 → a = ⊥ :=
    sigmaFinite_faithfulValuation (F i) (hF i)
  choose ρ hρ hf using H
  refine ⟨(∀ i, MmodN (F i)), inferInstance, product_hasFiniteValuationCover ρ hρ hf, ?_⟩
  exact ⟨(premapOrderIso f g hgf hfg).trans (coprodOrderIso F)⟩
end Gelfand454_part_Final
