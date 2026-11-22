-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_negative_mark_strict_preruin_finitecap_closed_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:50:44.377056+00:00
-- url     : https://prove2.me/submissions/4abfa66d-c3f9-4862-84b2-6ed9e720e0f2

/-
  A genuine negative jump before ruin has positive pre-jump reserves.
  The physical post-right-dividend left limit is inside the finite cap.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_strict_preruin_negative_mark_prestate_positive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hFin : C ≠ ⊤) (hxc : ENNReal.ofReal x ≤ C)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (htpos : 0 < t)
    (htpreruin : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hz : X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0) :
    0 < x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ∧
    x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ≤ C.toReal := by
  have hp :=
    avram_freshD_original_strict_preruin_negative_mark_prestate_positive
      X x D ω t htpreruin hz
  have hclosed :=
    avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
      X x C hxc D hD ω t (Or.inr htpreruin)
  have hEq :=
    avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD.1.1 ω t htpos
  have hCap : ENNReal.ofReal
      (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C := by
    simpa only [hEq] using hclosed.2
  have hr := ENNReal.toReal_mono hFin hCap
  rw [ENNReal.toReal_ofReal (le_of_lt hp)] at hr
  exact ⟨hp, hr⟩
