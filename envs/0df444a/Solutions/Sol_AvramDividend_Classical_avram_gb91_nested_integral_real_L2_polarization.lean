-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb91_nested_integral_real_L2_polarization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:50:40.395484+00:00
-- url     : https://prove2.me/submissions/31adfeb5-5166-464f-81be-5f1ee70a455a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb73_integral_L2_polarization
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ) (f g : ℝ → Ω → ℝ)
    (hinner : ∀ t : ℝ,
      Integrable (fun ω => (f t ω) ^ 2) P ∧
      Integrable (fun ω => (g t ω) ^ 2) P ∧
      Integrable (fun ω => f t ω * g t ω) P)
    (hf : IntegrableOn (fun t => ∫ ω, (f t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume)
    (hg : IntegrableOn (fun t => ∫ ω, (g t ω) ^ 2 ∂P)
      (Ioo (0 : ℝ) T) volume)
    (hfg : IntegrableOn (fun t => ∫ ω, f t ω * g t ω ∂P)
      (Ioo (0 : ℝ) T) volume) :
    (∫ t in Ioo (0 : ℝ) T,
      (∫ ω, (f t ω - g t ω) ^ 2 ∂P) ∂volume) =
      (∫ t in Ioo (0 : ℝ) T,
        (∫ ω, (f t ω) ^ 2 ∂P) ∂volume) +
      (∫ t in Ioo (0 : ℝ) T,
        (∫ ω, (g t ω) ^ 2 ∂P) ∂volume) -
      2 * (∫ t in Ioo (0 : ℝ) T,
        (∫ ω, f t ω * g t ω ∂P) ∂volume) := by
  have hpoint : ∀ t : ℝ,
      (∫ ω, (f t ω - g t ω) ^ 2 ∂P) =
        (∫ ω, (f t ω) ^ 2 ∂P) +
        (∫ ω, (g t ω) ^ 2 ∂P) -
        2 * (∫ ω, f t ω * g t ω ∂P) := by
    intro t
    obtain ⟨h1, h2, h3⟩ := hinner t
    exact avram_gb73_integral_L2_polarization P (f t) (g t) h1 h2 h3
  simp_rw [hpoint]
  erw [integral_sub (hf.add hg) (hfg.const_mul 2)]
  erw [integral_add hf hg]
  rw [integral_const_mul]
