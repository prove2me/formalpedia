-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_local_Borel_negative_mark_count_finite_ae_allactivity_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:49:29.368454+00:00
-- url     : https://prove2.me/submissions/5bf1e011-125c-43dc-ae22-7699f4536581

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) (hν : X.ν B < ⊤) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P, NX ω (Ioc s t ×ˢ B) < ⊤  := by
  intro NX
  let N : Ω → ℝ≥0∞ := fun ω => NX ω (Ioc s t ×ˢ B)
  have hMeas : Measurable N := by
    have hRaw :=
      avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X s (t - s) B hB
    have ht : s + (t - s) = t := add_tsub_cancel_of_le hst
    simpa only [N, NX, ht] using hRaw
  have hCamp :=
    avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
      X s t hst B hB hNeg
  change (∫⁻ ω, N ω ∂P) =
    ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B at hCamp
  have hIntFinite : (∫⁻ ω, N ω ∂P) < ⊤ := by
    rw [hCamp]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hν
  simpa only [N] using ae_lt_top hMeas (ne_of_lt hIntFinite)
