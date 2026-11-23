-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_spatial_Nat_count_ENNReal_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:27:18.378194+00:00
-- url     : https://prove2.me/submissions/9040ac4b-45a4-47c8-981b-3879b09e939d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
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
    (K : Fin n → Ω → ℕ)
    (hK : ∀ i, Measurable (K i))
    (hReal : ∀ᵐ ω ∂P, ∀ i,
      (K i ω : ℝ) =
        (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i)).toReal) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      (K i ω : ℝ≥0∞) =
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B i) := by
  classical
  apply ae_all_iff.mpr
  intro i
  have hSupport :=
    avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
      X hFinite t (B i) (hMeas i) (hNeg i) (K i) (hK i)
      ((ae_all_iff.mp hReal) i)
  filter_upwards [hSupport] with ω hω
  obtain ⟨S, hS, hCard⟩ := hω
  have hCount :=
    avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
      X ω t (B i) (hMeas i) S hS 0 t
      (zero_le : (0 : ℝ≥0) ≤ t) le_rfl
  have hFilter : S.filter (fun u => 0 < u ∧ u ≤ t) = S := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact ⟨((hS u).mp hu).1, ((hS u).mp hu).2.1⟩
  calc
    (K i ω : ℝ≥0∞) = (S.card : ℝ≥0∞) := by
      exact congrArg (fun k : ℕ => (k : ℝ≥0∞)) hCard
    _ = _ := by
      simpa only [hFilter] using hCount.symm
