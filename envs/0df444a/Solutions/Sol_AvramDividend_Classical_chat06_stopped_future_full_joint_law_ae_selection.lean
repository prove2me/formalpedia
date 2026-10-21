-- Prove2me | solution 1 for AvramDividend.Classical.chat06_stopped_future_full_joint_law_ae_selection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:04:40.47868+00:00
-- url     : https://prove2.me/submissions/a8fea458-ae5b-4a29-8fe0-8530b5fc8bcd

import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.Pi

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- An optional-stopping selection theorem for complete random
sequences. If the event choosing each index n is independent
of the *whole* random future sequence attached to n, and that
future sequence has one common law μ, then the randomly
selected future has law μ too. There is no unjustified
independence claim at the random stopping index. -/
theorem random_indexed_future_hasLaw_of_event_factorisation
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (F : ℕ → Ω → E) (hF : ∀ n, Measurable (F n))
    (μ : Measure E)
    (hFactor : ∀ n (B : Set E), MeasurableSet B →
      P ({ω | N ω = n} ∩ {ω | F n ω ∈ B}) =
        P {ω | N ω = n} * μ B) :
    HasLaw (fun ω => F (N ω) ω) μ P := by
  have hFn : Measurable (fun p : ℕ × Ω => F p.1 p.2) := by
    apply measurable_from_prod_countable_right
    intro n
    change Measurable (F n)
    exact hF n
  have hsel : Measurable (fun ω => F (N ω) ω) :=
    hFn.comp (hN.prodMk measurable_id)
  have hNm (n : ℕ) : MeasurableSet {ω | N ω = n} :=
    hN (measurableSet_singleton n)
  have hNd : Pairwise
      (fun i j : ℕ => Disjoint {ω | N ω = i} {ω | N ω = j}) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.symm.trans hj)
  have hNuniv : (⋃ n : ℕ, {ω | N ω = n}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨N ω, rfl⟩
  have hSum : (∑' n : ℕ, P {ω | N ω = n}) = 1 := by
    rw [← measure_iUnion hNd hNm, hNuniv, measure_univ]
  refine ⟨hsel.aemeasurable, ?_⟩
  apply Measure.ext fun B hB => ?_
  rw [Measure.map_apply hsel hB]
  let A (n : ℕ) : Set Ω :=
    {ω | N ω = n} ∩ {ω | F n ω ∈ B}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (hNm n).inter ((hF n) hB)
  have hAd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    exact (hNd hij).mono inter_subset_left inter_subset_left
  have hAeq :
      {ω | F (N ω) ω ∈ B} = ⋃ n : ℕ, A n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, A, Set.mem_inter]
    constructor
    · intro hb
      exact ⟨N ω, rfl, hb⟩
    · rintro ⟨n, hn, hb⟩
      change F n ω ∈ B at hb
      rw [hn]
      exact hb
  change P {ω | F (N ω) ω ∈ B} = μ B
  rw [hAeq, measure_iUnion hAd hAm]
  simp_rw [show ∀ n, P (A n) = P {ω | N ω = n} * μ B from
    fun n => hFactor n B hB]
  rw [ENNReal.tsum_mul_right, hSum, one_mul]


/-- A randomly selected infinite-dimensional future retains its
whole joint law if each selection event is only *almost surely*
an event of the observed past and the deterministic-index
future is independent of that past. Works with full-path
validity repairs of iid waiting sequences. -/
theorem stopped_future_hasLaw_of_ae_past_cylinder
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (past : ℕ → Ω → A) (future : ℕ → Ω → E)
    (hFuture : ∀ n, Measurable (future n))
    (hInd : ∀ n, IndepFun (past n) (future n) P)
    (μ : Measure E)
    (hLaw : ∀ n, HasLaw (future n) μ P)
    (hStop : ∀ n, ∃ S : Set A, MeasurableSet S ∧
      (fun ω : Ω => N ω = n) =ᵐ[P]
      (fun ω : Ω => past n ω ∈ S)) :
    HasLaw (fun ω => future (N ω) ω) μ P := by
  have hFactor : ∀ n (B : Set E), MeasurableSet B →
      P ({ω | N ω = n} ∩ {ω | future n ω ∈ B}) =
        P {ω | N ω = n} * μ B := by
    intro n B hB
    obtain ⟨S, hS, hEq⟩ := hStop n
    have hInter : (fun ω : Ω =>
        ω ∈ ({z | N z = n} ∩ {z | future n z ∈ B})) =ᵐ[P]
        (fun ω : Ω =>
          ω ∈ ((past n ⁻¹' S) ∩ (future n ⁻¹' B))) := by
      filter_upwards [hEq] with ω hω
      change ((N ω = n) ∧ future n ω ∈ B) =
        (past n ω ∈ S ∧ future n ω ∈ B)
      rw [hω]
    have hm : P {ω | N ω = n} = P (past n ⁻¹' S) :=
      measure_congr hEq
    have hf : P (future n ⁻¹' B) = μ B :=
      (hLaw n).measure_eq hB
    calc
      P ({ω | N ω = n} ∩ {ω | future n ω ∈ B}) =
          P (past n ⁻¹' S ∩ future n ⁻¹' B) :=
        measure_congr hInter
      _ = P (past n ⁻¹' S) * P (future n ⁻¹' B) :=
        (hInd n).measure_inter_preimage_eq_mul S B hS hB
      _ = P {ω | N ω = n} * μ B := by rw [← hm, hf]
  exact random_indexed_future_hasLaw_of_event_factorisation
    N hN future hFuture μ hFactor

end AvramChat06

open AvramChat06

theorem solution
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace A]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (past : ℕ → Ω → A) (future : ℕ → Ω → E)
    (hFuture : ∀ n, Measurable (future n))
    (hInd : ∀ n, IndepFun (past n) (future n) P)
    (μ : Measure E)
    (hLaw : ∀ n, HasLaw (future n) μ P)
    (hStop : ∀ n, ∃ S : Set A, MeasurableSet S ∧
      (fun ω : Ω => N ω = n) =ᵐ[P]
      (fun ω : Ω => past n ω ∈ S)) :
    HasLaw (fun ω => future (N ω) ω) μ P := by
  exact stopped_future_hasLaw_of_ae_past_cylinder
    N hN past future hFuture hInd μ hLaw hStop
