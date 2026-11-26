-- Prove2me | solution 1 for ClassicalComplexWPT.seqPreparedPolynomial_unique_of_eventually_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:19:42.439959+00:00
-- url     : https://prove2.me/submissions/a0280927-9a1e-41f5-80a3-633da2ab6c99

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Theorems.Thm_ClassicalComplexWPT_eq_of_evalL1PowerSeries_eventuallyEq
import Theorems.Thm_ClassicalComplexWPT_seqPreparedPolynomial_unique

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (d : ℕ)
    (p p' v : L1Coeff ℕ)
    (hp' : ‖p'‖ < 1)
    (hpLow : seqHighShift d p = 0)
    (hp'Low : seqHighShift d p' = 0)
    (heval :
      (fun w ↦ evalL1PowerSeries (seqLowShift d constantOneSeq + p) w) =ᶠ[nhds 0]
        (fun w ↦ evalL1PowerSeries
          (seqLowShift d v + convolution v p') w)) :
    p = p' ∧ v = constantOneSeq := by
  have hfactor :
      seqLowShift d constantOneSeq + p =
        seqLowShift d v + convolution v p' :=
    eq_of_evalL1PowerSeries_eventuallyEq _ _ heval
  exact seqPreparedPolynomial_unique d p p' v hp' hpLow hp'Low hfactor
end ClassicalComplexWPT
