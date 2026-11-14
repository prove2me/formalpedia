-- Prove2me | solution 1 for AvramDividend.Classical.avram_b50_original_negative_borel_simple_centered_exact_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:01:52.68742+00:00
-- url     : https://prove2.me/submissions/a269fea7-07e6-4154-87a2-422af11f2bcf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original simple marked compensated jump martingale has zero mean and exact variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range K, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K,
      i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((t : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 t ×ˢ B i)).toReal - r i
    let G : Ω → ℝ := fun ω => ∑ i ∈ Finset.range K, c i * Y i ω
    Integrable G P ∧
    (∫ ω, G ω ∂P) = 0 ∧
    Integrable (fun ω => (G ω)^2) P ∧
    (∫ ω, (G ω)^2 ∂P) =
      ∑ i ∈ Finset.range K, (c i)^2 * r i := by 
  classical
  have hMean :=
    avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
      X hFinite t K B c hB hNeg
  have hVar :=
    avram_ja31_original_finite_borel_mark_source_isometry
      X hFinite t (Finset.range K) B c hB hNeg hDisj
  exact ⟨hMean.1, hMean.2, hVar.1, hVar.2⟩
