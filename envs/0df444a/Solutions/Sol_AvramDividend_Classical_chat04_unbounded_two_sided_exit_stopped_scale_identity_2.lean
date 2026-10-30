-- Prove2me | solution 2 for AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:38:03.119039+00:00
-- url     : https://prove2.me/submissions/6b450f69-1f95-4288-a590-8641909e65f0

-- REPAIR ITERATION L of CE 15378 (5 groups, analysis d60cddaa); K bytes e5512eca
-- already in remote history (duplicate guard), so this is a differentiated
-- reduction variant testing the same causal hypothesis with a new hash.
-- Cause-linked fixes vs parent CE:
--   E01/E02: no `simp [X.BoundedVariation]`; hnbv passes through to the helper.
--   E03: same-barrier fold only (raw iInf = Up/Down wrappers at (a-x,-x)).
--   E04: no `W x = W 0`.
--   E05: no (a,0) zero-start reuse; general-reserve Open premise 2dcc8bcc only.
-- Reduction shape (sorry-free over one Open child): hFold identifies the raw
-- goal integral with twoSidedExitExpectation at identical (a-x,-x) barriers;
-- Open 2dcc8bcc (status Open verified via show; same binders/order as target)
-- closes the stopped balance. Expected: SKETCH_ACCEPTED (Open premise) or a
-- precise bridge CE on hFold.
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_two_sided_exit_expectation_scale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  -- Same-barrier fold: raw iInfs are definitionally the Up/Down wrappers
  -- at barriers (a - x) and (-x); cf. pinned TwoSidedExit definitions.
  have hFold : (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = twoSidedExitExpectation X q a x := by
    unfold twoSidedExitExpectation twoSidedExitUpTime twoSidedExitDownTime
    rfl
  -- Stopped balance at exact (a-x,-x) barriers (Open 2dcc8bcc, UBV direct).
  have hOST : twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) :=
    AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity
      X q hq W hW hnbv a x ha hx0 hxa
  rw [hFold]
  exact hOST
