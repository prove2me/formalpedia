-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys79_original_zero_marks_stopped_marked_jump_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:30:46.64382+00:00
-- url     : https://prove2.me/submissions/861f9224-abb1-4a72-b7e6-ebcd3590a0f1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original marked-jump contribution to the stopped finite-grid ledger,
on an event with no negative marks, is exactly minus its compensator. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (C : ℝ≥0∞) (q : ℝ) (w : ℝ → ℝ)
    (U : ℝ≥0 → Ω → ℝ)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    let H : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < (T : ℝ) - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧
         p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ n : ℕ,
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) =
      -(∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) := by
  intro H NX n
  have hMask : ∀ m (p : ℝ≥0 × ℝ),
      H m ((p.1, ω), p.2) ≠ 0 →
      0 < p.1 ∧ (p.1 : ℝ) < (T : ℝ) - δ m ∧ p.2 < 0 := by
    intro m p hp
    dsimp [H] at hp
    split_ifs at hp with h
    · exact ⟨h.1, h.2.1, h.2.2.2.2.2⟩
    · simp at hp
  have hz := avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
    X ω T δ hδ hZero H hMask n
  change (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) = _
  rw [hz]
  ring
