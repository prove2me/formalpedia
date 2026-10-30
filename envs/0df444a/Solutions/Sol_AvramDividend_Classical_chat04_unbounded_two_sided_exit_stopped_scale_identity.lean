-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_two_sided_exit_stopped_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:11:27.44353+00:00
-- url     : https://prove2.me/submissions/ce3e8790-f51c-42fa-bbfa-469f0e312d7f

-- REPAIR ITERATION K of CE 15378 (5 groups, analysis d60cddaa).
-- Cause-linked fixes vs parent:
--   E01/E02: no `simp [X.BoundedVariation]` (BV is a Prop conjunction, not a
--     simp lemma); hnbv is consumed inside Proved lemmas / the Open helper.
--   E03: no rfl across -x vs 0 down-barriers; hFold is the same-barrier
--     definitional fold (raw iInf = Up/Down wrappers) via unfold + rfl only.
--   E04: no `W x = W 0` by rfl.
--   E05: no hZero at (a,0) barriers reused for the (a-x,-x) goal.
-- Reduction shape (sorry-free over one Open child): hFold identifies the raw
-- goal integral with twoSidedExitExpectation at the same (a-x,-x) barriers;
-- the freshly PUBLISHED Open helper 2dcc8bcc (authored this thread, job
-- df1361e7, acyclic by construction: it cites no mission theorem) closes
-- the stopped balance. Expected verdict: SKETCH_ACCEPTED (Open premise) or
-- a precise bridge CE pinpointing hFold.
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
  -- Same-barrier fold: raw iInfs are definitionally the Up/Down wrappers.
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
  rw [hFold, hOST]
