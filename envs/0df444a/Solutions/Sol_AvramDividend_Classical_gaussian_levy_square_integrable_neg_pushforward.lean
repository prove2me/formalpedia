-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_square_integrable_neg_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:21:12.798933+00:00
-- url     : https://prove2.me/submissions/abc49052-0f6f-4315-bcd9-b20b1b702bbd

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Negation transports the negative-jump Lévy truncated-square
condition to the positive jump-magnitude pushforward measure. -/
theorem solution (ν : Measure ℝ)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(ν.map (fun y : ℝ => -y))) < ⊤ := by
  let n : ℝ → ℝ := fun y => -y
  let F : ℝ → ENNReal :=
    fun z => ENNReal.ofReal (min 1 (z ^ 2))
  have hn : Measurable n := measurable_id.neg
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hpre : n ⁻¹' Ioi (0 : ℝ) = Iio (0 : ℝ) := by
    ext y
    simp only [mem_preimage, mem_Ioi, mem_Iio, n]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hrestrict :
      (ν.map n).restrict (Ioi (0 : ℝ)) =
        (ν.restrict (Iio (0 : ℝ))).map n := by
    rw [Measure.restrict_map hn measurableSet_Ioi]
    rw [hpre]
  change (∫⁻ z : ℝ, F z ∂(ν.map n).restrict (Ioi (0 : ℝ))) < ⊤
  rw [hrestrict, lintegral_map hF hn]
  have hpow (y : ℝ) : (-y) ^ 2 = y ^ 2 := by ring
  simpa only [F, n, hpow] using hlevy
