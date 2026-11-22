-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finiteactivity_stopped_jump_support_prestate_allcap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:17:16.552301+00:00
-- url     : https://prove2.me/submissions/09bc9b5c-79a6-4c50-aa1a-981b2a26a8b0

/-
  General cap version of the original physical negative jump support and
  strict pre-ruin marked-reserve spatial mask, including infinite cap.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finiteactivity_negative_mark_times_exact_support_count
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
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ S : Ω → Finset ℝ≥0,
      ∀ᵐ ω ∂P,
        (∀ u : ℝ≥0, u ∈ S ω ↔
          0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0) ∧
        ((S ω).card : ℝ) =
          (((Measure.count.restrict {u : ℝ≥0 |
             0 < u ∧ X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 =>
                (u, X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal ∧
        (∀ t : ℝ≥0, t ∈ S ω →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 < Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t ∧
          ENNReal.ofReal (Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ≤ C)
:= by
  obtain ⟨S, hS⟩ :=
    avram_freshD_original_finiteactivity_negative_mark_times_exact_support_count
      X hFinite T
  refine ⟨S, ?_⟩
  filter_upwards [hS] with ω hω
  obtain ⟨hMem, hCount⟩ := hω
  refine ⟨hMem, hCount, ?_⟩
  intro t ht hpreruin
  obtain ⟨htpos, _, _, hz⟩ := (hMem t).mp ht
  have hPos :=
    avram_freshD_original_strict_preruin_negative_mark_prestate_positive
      X x D ω t hpreruin hz
  have hCap :=
    avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
      X x C hxc D hD ω t (Or.inr hpreruin)
  have hEq :=
    avram_wave3_04_postPaymentReserve_exact_leftLim_identity
      X x D hD.1.1 ω t htpos
  refine ⟨?_, hCap.2⟩
  simpa only [hEq] using hPos
