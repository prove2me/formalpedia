-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_marked_rectangle_generate_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:05:49.899579+00:00
-- url     : https://prove2.me/submissions/62690819-c3a0-49fa-bbc3-6680bdec806a

import Mathlib
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Probability.Process.Predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasurableSpace Set
open scoped ENNReal NNReal

/-- The genuinely adapted past-rectangle generator of the predictable
sigma-algebra, tensored with *all* measurable mark sets, generates the
exact marked predictable product sigma-algebra. The product generator
is countably spanning: the bottom-time atom and its future half-line
cover all time points. This is a structural sigma-generation theorem,
not a Campbell or Poisson-law hypothesis. -/
theorem solution
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ) :
    let G : Set (Set (ι × Ω)) :=
      {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                S = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                S = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    (𝓕.predictable).prod mE = MeasurableSpace.generateFrom GM := by
  classical
  let G : Set (Set (ι × Ω)) :=
    {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
              S = ({⊥} ×ˢ A)) ∨
         (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
              S = (Set.Ioi i ×ˢ A))}
  let GM : Set (Set ((ι × Ω) × E)) :=
    Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
  change (𝓕.predictable).prod mE = MeasurableSpace.generateFrom GM
  have hCount : IsCountablySpanning G := by
    refine ⟨fun n => if n = 0 then ({⊥} ×ˢ (Set.univ : Set Ω))
      else (Set.Ioi ⊥ ×ˢ (Set.univ : Set Ω)), ?_, ?_⟩
    · intro n
      by_cases hn : n = 0
      · simp only [hn, ↓reduceIte]
        exact Or.inl ⟨Set.univ, MeasurableSet.univ, rfl⟩
      · simp only [if_neg hn]
        exact Or.inr ⟨⊥, Set.univ, MeasurableSet.univ, rfl⟩
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x.1 = ⊥
      · refine ⟨0, ?_⟩
        simp [hx]
      · refine ⟨1, ?_⟩
        have hlt : (⊥ : ι) < x.1 :=
          lt_of_le_of_ne bot_le (Ne.symm hx)
        simp [hlt]
  letI : MeasurableSpace (ι × Ω) := 𝓕.predictable
  have hG : MeasurableSpace.generateFrom G = 𝓕.predictable := rfl
  have hProd : MeasurableSpace.generateFrom GM =
      @Prod.instMeasurableSpace (ι × Ω) E 𝓕.predictable mE := by
    exact generateFrom_eq_prod hG
      MeasurableSpace.generateFrom_measurableSet
      hCount isCountablySpanning_measurableSet
  rw [← Prod.instMeasurableSpace]
  exact hProd.symm
