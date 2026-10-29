-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_gap_descending_unscaled
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:22:32.756266+00:00
-- url     : https://prove2.me/submissions/858a45d4-f41c-4ed0-a489-b579fc7a4607

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_laplace_crossmul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual original-clock descending Laplace transform in the
strict moment gap, with both positive finite factors cancelled. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβ : 0 ≤ β) (hβlam : β < lam)
    (hgap : X.ψ β < p) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure p))) =
    ENNReal.ofReal ((p / lam) * ((lam - β) / (p - X.ψ β))) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let t : ℝ := p - X.ψ β
  let a : ℝ := lam - β
  let u : ℝ := (p / lam) * (a / t)
  let L : ℝ≥0∞ :=
    ∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure p))
  have ht : 0 < t := by dsimp [t]; linarith
  have ha : 0 < a := by dsimp [a]; linarith
  have hScaled :
      ENNReal.ofReal t * ENNReal.ofReal lam * L =
      ENNReal.ofReal a * ENNReal.ofReal p := by
    simpa only [t, a, L] using
      (avram_ws01e_bt_new_original_clock_descending_laplace_crossmul
        X p hp lam hlam hroot β hβ hβlam hgap)
  have hAlg :
      (t * lam) * u = a * p := by
    dsimp [u]
    field_simp [ne_of_gt ht, ne_of_gt hlam]
  have hCast :
      (ENNReal.ofReal t * ENNReal.ofReal lam) *
        ENNReal.ofReal u =
      ENNReal.ofReal a * ENNReal.ofReal p := by
    calc
      _ = ENNReal.ofReal ((t * lam) * u) := by
        rw [ENNReal.ofReal_mul (mul_pos ht hlam).le,
          ENNReal.ofReal_mul ht.le]
      _ = ENNReal.ofReal (a * p) := congrArg ENNReal.ofReal hAlg
      _ = _ := by rw [ENNReal.ofReal_mul ha.le]
  have hCross :
      (ENNReal.ofReal t * ENNReal.ofReal lam) * L =
      (ENNReal.ofReal t * ENNReal.ofReal lam) *
        ENNReal.ofReal u := by
    calc
      _ = ENNReal.ofReal t * ENNReal.ofReal lam * L := by ac_rfl
      _ = ENNReal.ofReal a * ENNReal.ofReal p := hScaled
      _ = _ := hCast.symm
  have hCoeff0 : ENNReal.ofReal t * ENNReal.ofReal lam ≠ 0 := by
    rw [← ENNReal.ofReal_mul ht.le]
    exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos ht hlam)
  have hCoeffTop : ENNReal.ofReal t * ENNReal.ofReal lam ≠ ⊤ := by
    rw [← ENNReal.ofReal_mul ht.le]
    exact ENNReal.ofReal_ne_top
  change L = ENNReal.ofReal u
  apply (ENNReal.mul_left_inj hCoeff0 hCoeffTop).mp
  simpa only [mul_comm, mul_assoc] using hCross
