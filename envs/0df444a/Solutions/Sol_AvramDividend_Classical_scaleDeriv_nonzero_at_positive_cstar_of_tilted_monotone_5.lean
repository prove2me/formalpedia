-- Prove2me | solution 5 for AvramDividend.Classical.scaleDeriv_nonzero_at_positive_cstar_of_tilted_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:06:48.941102+00:00
-- url     : https://prove2.me/submissions/c2b8e3bd-feaf-42c3-b626-4e70142cb99b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A positive finite extended-real barrier has a positive real representative;
the finite-barrier normaliser lemma then supplies the stated nonvanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
  have hfinite : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hc_real : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hc, hfinite⟩
  exact scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
    X hX q hq W hW hc_real hpos hdiff htilt

