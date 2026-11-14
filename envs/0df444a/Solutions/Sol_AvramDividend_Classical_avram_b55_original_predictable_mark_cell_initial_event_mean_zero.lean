-- Prove2me | solution 1 for AvramDividend.Classical.avram_b55_original_predictable_mark_cell_initial_event_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:13:25.513385+00:00
-- url     : https://prove2.me/submissions/edb399a8-7228-4dfd-8f58-990ca9c11548

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative Borel marked predictable cell integrates to zero on any genuine past event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B)
    (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
    (∫ ω in A, H ω * ((N ω).toReal - r) ∂P) = 0 := by 
  have hI :=
    (avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
      X T cut s t hst htT ε hε B hB hBand hCut H hH hHL2).1
  have h0 :=
    avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
      X T cut s t hst htT ε hε B hB hBand hCut H hH hHL2
  dsimp only at hI h0 ⊢
  refine ⟨hI, ?_⟩
  calc
    (∫ ω in A,
      H ω * (((((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) =
      ∫ ω in A, condExp (𝓕 s) P
        (fun η => H η * (((((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u η -
            Function.leftLim (fun v : ℝ≥0 => X.X v η) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u η -
            Function.leftLim (fun v : ℝ≥0 => X.X v η) u)))
          (Ioc s t ×ˢ B)).toReal) -
            (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) ω ∂P :=
      (setIntegral_condExp (𝓕.le s) hI hA).symm
    _ = 0 := integral_eq_zero_of_ae (ae_restrict_of_ae h0)
