-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_original_simpleFunc_physical_mark_fibre_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T16:29:00.841161+00:00
-- url     : https://prove2.me/submissions/771a1b09-20cc-4a13-a486-297602dff1ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a21_simple_mark_natural_fibre_partition_20261112
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_single_simple_fibre_from_partition
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (hSupport :
      ∀ᵐ ω ∂P, ∃ S : Finset ℝ≥0,
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) ∧
        J ω = ∑ u ∈ S,
          (X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u))
    (hCountLaw : ∀ (B : Set ℝ), MeasurableSet B →
      B ⊆ Iio (0 : ℝ) →
      (let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B)
       ∃ (K : Ω → ℕ) (r : ℝ≥0),
         Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
         (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
         (r : ℝ) = ((t : ℝ≥0∞) * X.ν B).toReal))
    (q : ℕ → SimpleFunc ℝ ℝ)
    (hNonpos : ∀ n y, q n y ≤ 0)
    :
    ∃ (f : ℕ → Ω → ℝ) (r : ℕ → ℝ),
      (∀ n, Measurable (f n)) ∧
      (∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) ∧
      (∀ᵐ ω ∂P, ∀ (n : ℕ) (S : Finset ℝ≥0),
        (∀ u, u ∈ S ↔ 0 < u ∧ u ≤ t ∧
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u ≠ 0) →
        f n ω = ∑ u ∈ S,
          q n (X.X u ω -
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u)) ∧
      (∀ n, r n = (t : ℝ) *
        (∫ y in Iio (0 : ℝ), Real.exp (q n y) - 1 ∂X.ν)) ∧
      ∀ n : ℕ, ∃ (k : ℕ) (B : Fin k → Set ℝ) (a : Fin k → ℝ),
        (∀ i, MeasurableSet (B i)) ∧
        (∀ i, B i ⊆ Iio (0 : ℝ)) ∧
        (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
        (∀ᵐ ω ∂P, f n ω =
          ∑ i : Fin k, a i *
            (((Measure.count.restrict {u : ℝ≥0 |
                0 < u ∧ X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 t ×ˢ B i)).toReal) ∧
        r n = ∑ i : Fin k,
          (((t : ℝ≥0∞) * X.ν (B i)).toReal) *
            (Real.exp (a i) - 1) := by
  classical
  let step (n : ℕ) :=
    AvramDividend.Classical.avram_bridge20261123_A77_original_single_simple_fibre_from_partition
      X hFinite t θ hθ J hJMeas hJEq hSupport hCountLaw
      (q n) (hNonpos n)
      (AvramDividend.Classical.avram_a21_simple_mark_natural_fibre_partition_20261112
        (Iio (0 : ℝ)) measurableSet_Iio (q n))
  let f : ℕ → Ω → ℝ := fun n => Classical.choose (step n)
  let r : ℕ → ℝ := fun n =>
    Classical.choose (Classical.choose_spec (step n))
  refine ⟨f, r, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (step n))).1
  · exact ae_all_iff.mpr (fun n =>
      (Classical.choose_spec (Classical.choose_spec (step n))).2.1)
  · exact ae_all_iff.mpr (fun n =>
      (Classical.choose_spec (Classical.choose_spec (step n))).2.2.1)
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (step n))).2.2.2.1
  · intro n
    exact (Classical.choose_spec (Classical.choose_spec (step n))).2.2.2.2
