-- Prove2me | solution 1 for AvramDividend.Classical.avram_original_negative_jump_strict_preruin_spatial_mask_allcap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:19:06.68655+00:00
-- url     : https://prove2.me/submissions/10ca0b73-f56e-4b38-a8b4-5e127d861ce8

/-
  Original intrinsic jump-prestate mask for any negative jump strictly
  before ruin, under an arbitrary extended-real cap and jump activity.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_strict_preruin_negative_mark_prestate_positive
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_exact_leftLim_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) (htpos : 0 < t)
    (htpreruin : (t : ℝ≥0∞) < ruinTime X x D ω)
    (hz : X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t < 0) :
    0 < Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
    ENNReal.ofReal (Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) ≤ C
:= by
  have hPos :=
    avram_freshD_original_strict_preruin_negative_mark_prestate_positive
      X x D ω t htpreruin hz
  have hCap :=
    avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
      X x C hxc D hD ω t (Or.inr htpreruin)
  have hEq :=
    avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD.1.1 ω t htpos
  refine ⟨?_, hCap.2⟩
  simpa only [hEq] using hPos
