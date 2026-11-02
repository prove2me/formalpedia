-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:44:34.349759+00:00
-- url     : https://prove2.me/submissions/4d904346-45d8-45c1-8707-05a5788b179c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- Every original finite-variation dividend strategy has only countably many
strictly positive right-payment atoms on any closed horizon, without a
finite-jump control assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    {t : ℝ≥0 | t ≤ T ∧ 0 < rightLimit D t ω - D t ω}.Countable := by
  classical
  rcases avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support
    X x D hD ω T (fun _ => (1 : ℝ≥0∞)) with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, hFull, hTsum, hSupport⟩
  have hInj : Function.Injective (fun t : ℝ≥0 => (t : ℝ)) :=
    NNReal.coe_injective
  have hPre : ((fun t : ℝ≥0 => (t : ℝ)) ⁻¹' A).Countable :=
    hCount.preimage hInj
  refine hPre.mono ?_
  intro t ht
  rcases ht with ⟨htT, htPay⟩
  apply hSupport (t : ℝ)
  rw [hAt t htT]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr htPay)
