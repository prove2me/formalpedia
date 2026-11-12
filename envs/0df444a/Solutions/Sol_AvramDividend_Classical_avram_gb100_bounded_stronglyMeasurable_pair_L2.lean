-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb100_bounded_stronglyMeasurable_pair_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:20:53.855968+00:00
-- url     : https://prove2.me/submissions/9108ede5-9c22-4687-bba0-087b51de07ad

import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f g : Ω → ℝ) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) (Bf Bg : ℝ)
    (hBf0 : 0 ≤ Bf) (hBg0 : 0 ≤ Bg)
    (hBf : ∀ ω, |f ω| ≤ Bf)
    (hBg : ∀ ω, |g ω| ≤ Bg) :
    Integrable (fun ω => (f ω) ^ 2) P ∧
    Integrable (fun ω => (g ω) ^ 2) P ∧
    Integrable (fun ω => f ω * g ω) P := by
  have hSq (h : Ω → ℝ) (hh : StronglyMeasurable h)
      (B : ℝ) (hB0 : 0 ≤ B) (hb : ∀ ω, |h ω| ≤ B) :
      Integrable (fun ω => (h ω) ^ 2) P := by
    apply Integrable.of_bound (hh.pow 2).aestronglyMeasurable (B ^ 2)
    filter_upwards [] with ω
    have hbd := hb ω
    have hsq : |h ω| ^ 2 ≤ B ^ 2 := by
      nlinarith [abs_nonneg (h ω)]
    simpa [Real.norm_eq_abs, abs_pow] using hsq
  refine ⟨hSq f hf Bf hBf0 hBf, hSq g hg Bg hBg0 hBg, ?_⟩
  apply Integrable.of_bound (hf.mul hg).aestronglyMeasurable (Bf * Bg)
  filter_upwards [] with ω
  simpa [Real.norm_eq_abs, abs_mul] using
    (mul_le_mul (hBf ω) (hBg ω) (abs_nonneg _) hBf0)
