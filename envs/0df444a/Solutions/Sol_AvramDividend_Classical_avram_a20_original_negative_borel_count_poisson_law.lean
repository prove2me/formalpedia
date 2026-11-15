-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_negative_borel_count_poisson_law
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:17:32.649901+00:00
-- url     : https://prove2.me/submissions/d9d04988-54c7-491d-aa65-a42d224efb9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_nat_count_realisation
import Theorems.Thm_AvramDividend_Classical_avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Nat
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    ∃ (K : Ω → ℕ) (r : ℝ≥0),
      Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
      (∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal) ∧
      (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal := by
  dsimp
  obtain ⟨K, hK, hCount⟩ :=
    avram_a20_original_negative_borel_nat_count_realisation
      X hFinite T B hB hNeg
  let r : ℝ≥0 :=
    ⟨((T : ℝ≥0∞) * X.ν B).toReal, ENNReal.toReal_nonneg⟩
  have hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal := rfl
  have hMass (k : ℕ) :
      P {ω : Ω | K ω = k} = poissonMeasure r {k} :=
    avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
      X hFinite T B hB hNeg K hK hCount r hr k
  have hLaw : HasLaw K (poissonMeasure r) P := by
    refine ⟨hK.aemeasurable, ?_⟩
    apply Measure.ext_of_singleton
    intro k
    rw [Measure.map_apply hK (measurableSet_singleton k)]
    exact hMass k
  exact ⟨K, r, hK, hLaw, hCount, hr⟩
