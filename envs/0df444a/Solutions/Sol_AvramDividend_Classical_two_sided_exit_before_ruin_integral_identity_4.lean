-- Prove2me | solution 4 for AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:43:44.875675+00:00
-- url     : https://prove2.me/submissions/35244c8f-cde7-449f-b8e6-c78e16ff2f1f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_stopped_scale_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open AvramDividend.Classical

/-!
# The two-sided exit identity before ruin, in expanded form

Avram–Palmowski–Pistorius (2007), equation (3.6) and Proposition 1,
pp. 6–8: for a spectrally negative Lévy process started from `x ∈ [0, a]`,
the discounted expectation of the strict upward exit from `[0, a]`, restricted
to the event that the upward exit happens *before* the first downward exit
below `0`, is

    W^(q)(x) / W^(q)(a).

This target states the integral with the first-passage infima written out, so
that it needs no local preamble definitions.  The proof reduces it to the
mission's own authoritative child

    AvramDividend.Classical.two_sided_exit_stopped_scale_identity
    (09663d0d)

which states the *same* discounted integral multiplied by
`ENNReal.ofReal (W a)` equal to `ENNReal.ofReal (W x)`.  The two statements
differ only by the factor `ENNReal.ofReal (W a)`, so the reduction is:

1. the Proved `scaleFunction_strict_pos_of_standing` gives `0 < W a` for
   `a > 0`, so `ENNReal.ofReal (W a)` is a finite non-zero element of
   `ℝ≥0∞` and division by it is legitimate;
2. the imported identity is divided by `ENNReal.ofReal (W a)` using
   `ENNReal.mul_div_cancel_right`;
3. `ENNReal.ofReal_div_of_pos` identifies the `ℝ≥0∞` quotient with the
   `ENNReal.ofReal (W x / W a)` of the target.

The imported child is still **Open**: its substantive content is the
stopped `q`-scale martingale identity of the paper (the two-sided exit
martingale, equation (3.6)).  The catalogue's own decomposition of the goal
`88d146b8` shows that this identity — via the `chat03_grid_stopped_scale_*`
family — is the root obstruction for the whole mission.  So this candidate
is a source-faithful *reduction*, not a proof: it is expected to return
`SKETCH_ACCEPTED`, and the target stays `Open` until the imported child is
discharged.
-/

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) =
      ENNReal.ofReal (W x / W a) := by
  -- The scale function is strictly positive at a positive level.
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  -- The imported stopped-scale identity, in the same expanded form.
  have hstop :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x) :=
    two_sided_exit_stopped_scale_identity X hX q hq W hW a x ha hx0 hxa
  -- The denominator is a finite non-zero element of `ℝ≥0∞`.
  have hden0 : ENNReal.ofReal (W a) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hWa)
  have hdenTop : ENNReal.ofReal (W a) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Divide the identity by `ENNReal.ofReal (W a)`.
  have hdiv :
      (∫⁻ ω,
        if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
            (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) =
        ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by
    calc
      (∫⁻ ω,
          if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
              (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
            ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
          else 0 ∂P) =
          ((∫⁻ ω,
              if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
                  (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
                ENNReal.ofReal
                  (Real.exp (-(q * ENNReal.toReal
                    (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
              else 0 ∂P) * ENNReal.ofReal (W a)) / ENNReal.ofReal (W a) := by
                symm
                exact ENNReal.mul_div_cancel_right hden0 hdenTop
      _ = ENNReal.ofReal (W x) / ENNReal.ofReal (W a) := by rw [hstop]
  simpa only [ENNReal.ofReal_div_of_pos hWa] using hdiv
