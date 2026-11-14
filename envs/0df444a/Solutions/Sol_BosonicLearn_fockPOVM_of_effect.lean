-- Prove2me | solution 1 for BosonicLearn.fockPOVM_of_effect
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:12:09.343192+00:00
-- url     : https://prove2.me/submissions/a77d9b50-4eed-450f-af27-ec2186c4bb42

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM
import Theorems.Thm_BosonicLearn_measure_of_uniform_limit
import Theorems.Thm_BosonicLearn_born_truncation

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open MeasureTheory
open scoped ENNReal Matrix
open Filter Topology

open BosonicLearn

noncomputable section

/-- A non-negative countably additive real set function is a finite measure. -/
private lemma measure_of_hasSum {Ω : Type} [MeasurableSpace Ω] (f : Set Ω → ℝ)
    (h0 : ∀ C, MeasurableSet C → 0 ≤ f C)
    (hσ : ∀ g : ℕ → Set Ω, (∀ n, MeasurableSet (g n)) → Pairwise (Function.onFun Disjoint g) →
      HasSum (fun n => f (g n)) (f (⋃ n, g n))) :
    ∃ μ : Measure Ω, IsFiniteMeasure μ ∧ ∀ C, MeasurableSet C → μ C = ENNReal.ofReal (f C) := by
  have hempty : f ∅ = 0 := by
    have h := hσ (fun _ => ∅) (fun _ => MeasurableSet.empty) (fun i j _ => by simp [Function.onFun])
    simp only [Set.iUnion_empty] at h
    have hs := h.summable
    rw [summable_const_iff] at hs
    exact hs
  refine ⟨Measure.ofMeasurable (fun C _ => ENNReal.ofReal (f C)) (by simp [hempty]) ?_, ⟨?_⟩,
    fun C hC => Measure.ofMeasurable_apply C hC⟩
  · intro g hg hd
    have h := hσ g hg hd
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => h0 _ (hg n)) h.summable]
  · rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
    exact ENNReal.ofReal_lt_top

/-- The trace of a density operator against the identity is `1`. -/
private lemma born_one {I : Type} [DecidableEq I] {X : Matrix I I ℂ} (hX : IsDensity X) :
    (∑' i, ∑' j, (1 : Matrix I I ℂ) i j * X j i).re = 1 := by
  have hdiag : ∀ i, (X i i).im = 0 := by
    intro i
    have h := hX.2.1 {i} (Pi.single i 1)
    simpa using h.1
  have hin : ∀ i, ∑' j, (1 : Matrix I I ℂ) i j * X j i = (((X i i).re : ℝ) : ℂ) := by
    intro i
    rw [tsum_eq_single i (fun j hj => by simp [Ne.symm hj])]
    simp only [Matrix.one_apply_eq, one_mul]
    exact Complex.ext (by simp) (by simp [hdiag i])
  rw [tsum_congr hin, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact hX.2.2.2

theorem solution {I Ω : Type} [DecidableEq I] [MeasurableSpace Ω] (E : Set Ω → Matrix I I ℂ)
    (hform : ∀ B : Set Ω, MeasurableSet B → ∀ (s : Finset I) (z : I → ℂ),
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j).im = 0 ∧
      0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j).re ∧
      (∑ i ∈ s, ∑ j ∈ s, star (z i) * E B i j * z j).re ≤ ∑ i ∈ s, ‖z i‖ ^ 2)
    (huniv : E Set.univ = 1)
    (hadd : ∀ (i j : I) (f : ℕ → Set Ω), (∀ n, MeasurableSet (f n)) →
      Pairwise (Function.onFun Disjoint f) → HasSum (fun n => E (f n) i j) (E (⋃ n, f n) i j)) :
    ∃ P : FockPOVM I Ω, P.effect = E := by
  have key : ∀ X : Matrix I I ℂ, IsDensity X → ∃ μ : Measure Ω, IsProbabilityMeasure μ ∧
      ∀ B, MeasurableSet B → μ B = ENNReal.ofReal (∑' i, ∑' j, E B i j * X j i).re := by
    intro X hX
    obtain ⟨h1, h2, -⟩ := born_truncation X hX
    choose F hF using fun n : ℕ => h1 (1 / ((n : ℝ) + 1)) (by positivity)
    have hlam : ∀ n, ∃ m : Measure Ω, IsFiniteMeasure m ∧ ∀ C, MeasurableSet C →
        m C = ENNReal.ofReal (∑ i ∈ F n, ∑ j ∈ F n, E C i j * X j i).re := by
      intro n
      refine measure_of_hasSum (fun C => (∑ i ∈ F n, ∑ j ∈ F n, E C i j * X j i).re)
        (fun C hC => (h2 (F n) (E C) (hform C hC)).2) fun f hf hd => ?_
      have h : HasSum (fun k => ∑ i ∈ F n, ∑ j ∈ F n, E (f k) i j * X j i)
          (∑ i ∈ F n, ∑ j ∈ F n, E (⋃ k, f k) i j * X j i) :=
        hasSum_sum fun i _ => hasSum_sum fun j _ => (hadd i j f hf hd).mul_right (X j i)
      exact Complex.reCLM.hasSum h
    choose lam hlamfin hlamval using hlam
    obtain ⟨μ, -, hμ⟩ := measure_of_uniform_limit (fun C => (∑' i, ∑' j, E C i j * X j i).re) lam
      hlamfin (fun n => 1 / ((n : ℝ) + 1)) tendsto_one_div_add_atTop_nhds_zero_nat (by
        intro n C hC
        rw [hlamval n C hC, ENNReal.toReal_ofReal (h2 (F n) (E C) (hform C hC)).2, ← Complex.sub_re]
        exact (Complex.abs_re_le_norm _).trans (hF n (F n) subset_rfl (E C) (hform C hC)))
    refine ⟨μ, ⟨?_⟩, hμ⟩
    rw [hμ _ MeasurableSet.univ, huniv, born_one hX, ENNReal.ofReal_one]
  choose! μ hμ using key
  exact ⟨{ effect := E, effect_form := hform, effect_univ := huniv, law := μ,
           law_prob := fun ρ hρ => (hμ ρ hρ).1, law_born := fun ρ hρ => (hμ ρ hρ).2 }, rfl⟩
