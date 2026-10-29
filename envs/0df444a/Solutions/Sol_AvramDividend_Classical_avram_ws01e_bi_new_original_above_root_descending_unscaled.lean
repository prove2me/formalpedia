-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_original_above_root_descending_unscaled
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:26:03.994704+00:00
-- url     : https://prove2.me/submissions/141eae71-e8c5-4c99-a9d9-6f6acb8c5a5d

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_above_root_descending_scaled

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact original-clock descending transform above the positive root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m β : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hβ : φ + lam < β)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure (p + q)))) =
    ENNReal.ofReal
      (((p + q) / (φ + lam)) *
        ((φ + lam - β) / (p + q - X.ψ β))) := by
  let a : ℝ := φ + lam
  let r : ℝ := p + q
  let u : ℝ := (a - β) / (r - X.ψ β)
  let L : ℝ≥0∞ := ∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂(P.prod (expMeasure (p + q)))
  have ha : 0 < a := by dsimp [a]; linarith
  have hr : 0 < r := by dsimp [r]; linarith
  have hScaled :
      ENNReal.ofReal a * (ENNReal.ofReal p * L) =
      ENNReal.ofReal r *
        (ENNReal.ofReal lam * ENNReal.ofReal ((p / lam) * u)) := by
    simpa only [a, r, u, L] using
      (avram_ws01e_bi_new_original_above_root_descending_scaled
        X q φ p lam m β hq hφ hroot hp hlam hlamroot
        hm hmderiv hβ hJoint)
  have hAlg (v : ℝ) : r * (lam * ((p / lam) * v)) =
      a * (p * ((r / a) * v)) := by
    field_simp [ne_of_gt ha, ne_of_gt hlam] <;> ring
  have hCast (v : ℝ) :
      ENNReal.ofReal r *
        (ENNReal.ofReal lam * ENNReal.ofReal ((p / lam) * v)) =
      ENNReal.ofReal a *
        (ENNReal.ofReal p * ENNReal.ofReal ((r / a) * v)) := by
    calc
      _ = ENNReal.ofReal (r * (lam * ((p / lam) * v))) := by
        rw [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_mul hlam.le]
      _ = ENNReal.ofReal (a * (p * ((r / a) * v))) :=
        congrArg ENNReal.ofReal (hAlg v)
      _ = _ := by rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul hp.le]
  have hCross :
      (ENNReal.ofReal a * ENNReal.ofReal p) * L =
      (ENNReal.ofReal a * ENNReal.ofReal p) *
        ENNReal.ofReal ((r / a) * u) := by
    calc
      _ = ENNReal.ofReal a * (ENNReal.ofReal p * L) := by ac_rfl
      _ = ENNReal.ofReal r *
          (ENNReal.ofReal lam * ENNReal.ofReal ((p / lam) * u)) := hScaled
      _ = ENNReal.ofReal a *
          (ENNReal.ofReal p * ENNReal.ofReal ((r / a) * u)) := hCast u
      _ = _ := by ac_rfl
  have hCoeff0 : ENNReal.ofReal a * ENNReal.ofReal p ≠ 0 := by
    rw [← ENNReal.ofReal_mul ha.le]; exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos ha hp)
  have hCoeffTop : ENNReal.ofReal a * ENNReal.ofReal p ≠ ⊤ := by
    rw [← ENNReal.ofReal_mul ha.le]; exact ENNReal.ofReal_ne_top
  change L = ENNReal.ofReal ((r / a) * u)
  exact (ENNReal.mul_left_inj hCoeff0 hCoeffTop).mp (by simpa only [mul_comm, mul_assoc] using hCross)
