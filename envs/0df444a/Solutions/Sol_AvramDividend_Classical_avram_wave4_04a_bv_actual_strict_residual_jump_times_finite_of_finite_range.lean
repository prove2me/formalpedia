-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:23:27.088002+00:00
-- url     : https://prove2.me/submissions/a0782f75-6379-4fbf-8e6f-65a0570d652b

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical

/--
On an original-path full event, a BV spectrally negative Lévy residual
with finite range on [0,T] has finitely many strict residual jump times.
The needed finite-range event is an explicit source-path hypothesis.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∃ S : Finset ℝ,
      ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ) * X.drift - X.X t ω ∈ S) :
    ∀ᵐ ω ∂P,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          Function.leftLim
            (fun u : ℝ≥0 => (u : ℝ) * X.drift - X.X u ω) t <
            (t : ℝ) * X.drift - X.X t ω}.Finite := by
  classical
  filter_upwards
    [bv_actual_levy_residual_ae_monotone_all_times X hBV, hRange]
    with ω hmono hω
  obtain ⟨S, hS⟩ := hω
  let Y : ℝ≥0 → ℝ := fun t => (t : ℝ) * X.drift - X.X t ω
  let J : Set ℝ≥0 :=
    {t : ℝ≥0 | t ≤ T ∧ 0 < t ∧ Function.leftLim Y t < Y t}
  change J.Finite
  let f : J → S := fun u => ⟨Y u.1, hS u.1 u.property.1⟩
  have hinj : Function.Injective f := by
    intro u v huv
    have heq : Y u.1 = Y v.1 := congrArg Subtype.val huv
    apply Subtype.ext
    rcases lt_trichotomy u.1 v.1 with hlt | hsame | hgt
    · have hstrict : Y u.1 < Y v.1 :=
        lt_of_le_of_lt (hmono.le_leftLim hlt) v.property.2.2
      exact False.elim ((ne_of_lt hstrict) heq)
    · exact hsame
    · have hstrict : Y v.1 < Y u.1 :=
        lt_of_le_of_lt (hmono.le_leftLim hgt) u.property.2.2
      exact False.elim ((ne_of_lt hstrict) heq.symm)
  letI : Finite J := Finite.of_injective f hinj
  exact Set.toFinite J
