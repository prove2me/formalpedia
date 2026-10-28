-- Prove2me | solution 1 for AvramDividend.Classical.levy_esscher_root_resolvent_ratio_pos_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:09:27.587173+00:00
-- url     : https://prove2.me/submissions/522ecf94-fb56-47dd-b4e0-d59ad09cb979

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ β : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hβ : 0 < β)
    (hroot : X.ψ φ = q) :
    0 < β / (X.ψ (φ + β) - q) ∧
      β / (X.ψ (φ + β) - q) ≤ φ / q := by
  have hsec := levy_psi_root_shifted_increment_lower
    X q φ β hq hφ hβ hroot
  have hden := sub_pos.mpr
    (levy_psi_root_strictly_above_shift X q φ β hq hφ hβ hroot)
  constructor
  · exact div_pos hβ hden
  · have hmul : (q / φ) * β * φ ≤
        (X.ψ (φ + β) - q) * φ :=
      mul_le_mul_of_nonneg_right hsec hφ.le
    have hprod : q * β ≤ (X.ψ (φ + β) - q) * φ := by
      calc
        q * β = (q / φ) * β * φ := by
          field_simp [ne_of_gt hφ]
        _ ≤ (X.ψ (φ + β) - q) * φ := hmul
    apply (div_le_div_iff₀ hden hq).2
    nlinarith [hprod]
