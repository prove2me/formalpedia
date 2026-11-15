-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB58_original_caplinear_initial_right_atom_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:29:26.784574+00:00
-- url     : https://prove2.me/submissions/9c5ba8d4-f30f-49c7-bb73-091023a845d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB24_interior_caplinear_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (b : ℝ)
    (hsec : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b →
      t - s ≤ w t - w s)
    (ω : Ω) :
    rightLimit D 0 ω +
      (if x - rightLimit D 0 ω ≤ b then
        w (x - rightLimit D 0 ω)
       else w b + ((x - rightLimit D 0 ω) - b)) ≤
    (if x ≤ b then w x else w b + (x - b)) := by
  have hInit :=
    avram_p4_e_localise_original_initial_postpayment_reserve_between_zero_and_book
      X x D hD.1 ω
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  have hPost : 0 ≤ x - rightLimit D 0 ω := by
    simpa only [hX0, add_zero] using hInit.2.1
  have hPre : x - rightLimit D 0 ω ≤ x := by
    simpa only [hX0, add_zero] using hInit.2.2
  have hSec :=
    avram_gbB24_interior_caplinear_global_secant
      w b hsec (x - rightLimit D 0 ω) x hPost hPre
  linarith
