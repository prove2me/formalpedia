-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_Poisson_witness_no_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:22:08.352117+00:00
-- url     : https://prove2.me/submissions/6031fad2-9347-4abd-88bc-fd5d44eb505c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_poisson_law
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hMeas : ∀ i, MeasurableSet (B i))
    (hNeg : ∀ i, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ (K : Fin n → Ω → ℕ) (r : Fin n → ℝ≥0),
      (∀ i, Measurable (K i)) ∧
      (∀ i, HasLaw (K i) (poissonMeasure (r i)) P) ∧
      (∀ᵐ ω ∂P, ∀ i, (K i ω : ℝ) =
        (NX ω (Ioc 0 t ×ˢ B i)).toReal) ∧
      (∀ i, (r i : ℝ) =
        ((t : ℝ≥0∞) * X.ν (B i)).toReal) := by
  classical
  dsimp only
  have hEach (i : Fin n) :
      ∃ (K : Ω → ℕ) (r : ℝ≥0),
        Measurable K ∧ HasLaw K (poissonMeasure r) P ∧
        (∀ᵐ ω ∂P, (K ω : ℝ) =
          (((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 t ×ˢ B i)).toReal) ∧
        (r : ℝ) = ((t : ℝ≥0∞) * X.ν (B i)).toReal := by
    exact avram_a20_original_negative_borel_count_poisson_law
      X hFinite t (B i) (hMeas i) (hNeg i)
  choose K r hMeasK hLaw hEq hRate using hEach
  refine ⟨K, r, hMeasK, hLaw, ?_, hRate⟩
  exact ae_all_iff.mpr hEq
