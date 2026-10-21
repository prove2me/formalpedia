-- Prove2me | solution 1 for AvramDividend.Classical.levy_increment_condExp_finite_simple_state
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:49:04.93652+00:00
-- url     : https://prove2.me/submissions/65fcd4bd-a7dd-451b-b3f7-17a93c134ecb

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_on_past_event

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f)
    (A : ι → Set Ω)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 s] (A i))
    (hI : ∀ i ∈ S,
      Integrable (fun ω => f (x i + X.X (t - s) ω)) P) :
    P[(fun ω => ∑ i ∈ S,
      (A i).indicator
        (fun ω' => f (x i + (X.X t ω' - X.X s ω'))) ω) | 𝓕 s] =ᵐ[P]
      (fun ω => ∑ i ∈ S,
        (A i).indicator
          (fun _ => ∫ ω', f (x i + X.X (t - s) ω') ∂P) ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let F : ι → Ω → ℝ := fun i ω =>
    f (x i + (X.X t ω - X.X s ω))
  let E : ι → ℝ := fun i =>
    ∫ ω, f (x i + X.X (t - s) ω) ∂P
  have hIntPiece : ∀ i ∈ S, Integrable ((A i).indicator (F i)) P := by
    intro i hi
    have hmeas : Measurable (fun z : ℝ => f (x i + z)) :=
      hf.comp (measurable_const.add measurable_id)
    have hid : IdentDistrib (F i)
        (fun ω => f (x i + X.X (t - s) ω)) P P := by
      simpa only [Function.comp_def, F] using
        (X.stationaryIncrements s t hst).comp hmeas
    have hFi : Integrable (F i) P := hid.integrable_iff.mpr (hI i hi)
    have hMeas : MeasurableSet (A i) :=
      (𝓕.le s) (A i) (hA i hi)
    exact hFi.indicator hMeas
  have hEach : ∀ i ∈ S,
      P[(A i).indicator (F i) | 𝓕 s] =ᵐ[P]
        (A i).indicator (fun _ => E i) := by
    intro i hi
    exact levy_increment_condExp_Borel_on_past_event
      X s t hst (x i) f hf (A i) (hA i hi) (hI i hi)
  have hAll (T : Finset ι) :
      T ⊆ S →
      (Integrable (fun ω => ∑ i ∈ T, (A i).indicator (F i) ω) P ∧
       P[(fun ω => ∑ i ∈ T, (A i).indicator (F i) ω) | 𝓕 s] =ᵐ[P]
         (fun ω => ∑ i ∈ T, (A i).indicator (fun _ => E i) ω)) := by
    induction T using Finset.induction_on with
    | empty =>
        intro _
        constructor
        · simpa using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) P)
        · simp
    | @insert a T ha ih =>
        intro hsub
        have has : a ∈ S := hsub (Finset.mem_insert_self a T)
        have hts : T ⊆ S := by
          intro i hi
          exact hsub (Finset.mem_insert_of_mem hi)
        obtain ⟨hIntT, hCT⟩ := ih hts
        have hIntA := hIntPiece a has
        have hCA := hEach a has
        have hSum : Integrable
            (fun ω => (A a).indicator (F a) ω +
              (∑ i ∈ T, (A i).indicator (F i) ω)) P :=
          hIntA.add hIntT
        have hCSum :=
          MeasureTheory.condExp_add hIntA hIntT (𝓕 s)
        constructor
        · simpa only [Finset.sum_insert ha] using hSum
        · simp only [Finset.sum_insert ha]
          change P[(A a).indicator (F a) +
            (fun ω => ∑ i ∈ T, (A i).indicator (F i) ω) | 𝓕 s] =ᵐ[P]
              ((A a).indicator (fun _ => E a) +
                (fun ω => ∑ i ∈ T, (A i).indicator (fun _ => E i) ω))
          exact hCSum.trans (hCA.add hCT)
  exact (hAll S (Finset.Subset.refl S)).2
