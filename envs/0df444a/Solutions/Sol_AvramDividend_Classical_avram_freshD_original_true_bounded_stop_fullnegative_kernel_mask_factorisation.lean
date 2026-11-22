-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_true_bounded_stop_fullnegative_kernel_mask_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:44:54.820793+00:00
-- url     : https://prove2.me/submissions/ec77e6f4-c1cd-4386-bd59-c57d26023104

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
    let μT : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Icc 0 (n : ℝ))).map Real.toNNReal
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    ∀ p : (ℝ≥0 × Ω) × ℝ,
      H p =
        (((if p.1.1 ≤ (n : ℝ≥0)
            then Real.exp (-(q * (p.1.1 : ℝ))) else 0) *
          (if (p.1.1 : ℝ≥0∞) ≤ (σ p.1.2 : ℝ≥0∞)
            then (1 : ℝ) else 0)) *
          ((if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2
            then (1 : ℝ) else 0) *
           (w (Y p.1 + p.2) - w (Y p.1)))) *
          (if 0 < p.1.1 ∧ 0 ≤ Y p.1 ∧
              ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0
           then (1 : ℝ) else 0) := by
  classical
  intro Y NX μT H p
  by_cases hclock : p.1.1 ≤ σ p.1.2
  · have hn : p.1.1 ≤ (n : ℝ≥0) :=
      le_trans hclock (hσbound p.1.2)
    by_cases ht : 0 < p.1.1 <;>
      by_cases hz : p.2 < 0 <;>
      by_cases hy : 0 ≤ Y p.1 <;>
      by_cases hc : ENNReal.ofReal (Y p.1) ≤ C <;>
      simp [H, hclock, hn, ht, hz, hy, hc,
        and_assoc, and_left_comm, and_comm]
  · simp [H, hclock]
