-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict10_discard_nonL1_negative_generator_before_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:43:06.13219+00:00
-- url     : https://prove2.me/submissions/ba2f5c0c-6b0b-442a-936d-e20c95a74571

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Discard a negative signed generator on the original event before
    integration; no L1 assumption on the signed generator is needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F M B ErrCell ErrContact : Ω → ℝ) (base : ℝ)
    (hM : Integrable M P) (hMzero : (∫ ω, M ω ∂P) = 0)
    (hCell : Integrable (fun ω => max (ErrCell ω) 0) P)
    (hContact : Integrable (fun ω => max (ErrContact ω) 0) P)
    (hFmeas : AEStronglyMeasurable F P)
    (hFnonneg : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hBnonpos : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hBudget : ∀ᵐ ω ∂P,
      F ω ≤ base + (M ω + B ω) +
        max (ErrCell ω) 0 + max (ErrContact ω) 0) :
    Integrable F P ∧
      (∫ ω, F ω ∂P) ≤
        base + (∫ ω, max (ErrCell ω) 0 ∂P) +
          (∫ ω, max (ErrContact ω) 0 ∂P) := by
  classical
  let H : Ω → ℝ := fun ω =>
    max (ErrCell ω) 0 + max (ErrContact ω) 0
  let G : Ω → ℝ := fun ω => base + M ω + H ω
  have hH : Integrable H P := hCell.add hContact
  have hG : Integrable G P :=
    ((integrable_const base).add hM).add hH
  have hUpper : ∀ᵐ ω ∂P, F ω ≤ G ω := by
    filter_upwards [hBnonpos, hBudget] with ω hBω hω
    change F ω ≤ base + M ω + H ω
    dsimp [H]
    linarith
  have hNorm : ∀ᵐ ω ∂P, ‖F ω‖ ≤ G ω := by
    filter_upwards [hFnonneg, hUpper] with ω hFω hω
    have hGω : 0 ≤ G ω := le_trans hFω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hFω] using hω
  have hFI : Integrable F P := hG.mono' hFmeas hNorm
  refine ⟨hFI, ?_⟩
  have hI := integral_mono_ae hFI hG hUpper
  change (∫ ω, F ω ∂P) ≤
      (∫ ω, base + M ω + H ω ∂P) at hI
  have hEvaluate :
      (∫ ω, base + M ω + H ω ∂P) =
        base + (∫ ω, max (ErrCell ω) 0 ∂P) +
          (∫ ω, max (ErrContact ω) 0 ∂P) := by
    calc
      (∫ ω, base + M ω + H ω ∂P) =
          (∫ ω, base + M ω ∂P) +
            (∫ ω, H ω ∂P) := by
        simpa only [Pi.add_apply] using
          (integral_add ((integrable_const base).add hM) hH)
      _ = ((∫ ω, base ∂P) + (∫ ω, M ω ∂P)) +
            (∫ ω, H ω ∂P) := by
        congr 1
        simpa only [Pi.add_apply] using
          (integral_add (integrable_const base) hM)
      _ = base + (∫ ω, max (ErrCell ω) 0 ∂P) +
            (∫ ω, max (ErrContact ω) 0 ∂P) := by
        have hHsum :
            (∫ ω, H ω ∂P) =
              (∫ ω, max (ErrCell ω) 0 ∂P) +
                (∫ ω, max (ErrContact ω) 0 ∂P) := by
          simpa only [H, Pi.add_apply] using
            (integral_add hCell hContact)
        have hPuniv : P.real Set.univ = 1 := by simp
        simp [integral_const, hMzero, hHsum, hPuniv, add_assoc]
  exact hI.trans_eq hEvaluate
