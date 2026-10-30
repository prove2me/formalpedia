-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_two_sided_exit_expectation_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:18:37.558392+00:00
-- url     : https://prove2.me/submissions/cd40f077-316f-4e10-91e7-3f622e4e24a8

-- Proof of helper 2dcc8bcc (Open): two-sided exit expectation scale identity.
-- Route: the raw two-leg stopped integral equals both sides.
--   Proved 5b55cf54 (factorisation, UBV direct): legs = E * ofReal (W a).
--   Open be9dc931 (stopped harmonicity, general reserve): legs = ofReal (W x).
-- Transitivity closes the goal. Exactly one Open premise (be9dc931), cited by
-- import; acyclic: be9dc931 is a standalone harmonicity statement.
-- Expected verdict: SKETCH_ACCEPTED (Open premise) or precise CE on the
-- trans step if the two legs-integrals differ syntactically.
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_harmonicity_general_reserve

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
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
      ENNReal.ofReal (W x) := by
  have hFactor : (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) =
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) :=
    AvramDividend.Classical.chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
      X hnbv q hq W hW a x hxa
  have hHarm : (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W x) :=
    AvramDividend.Classical.chat04_unbounded_stopped_scale_harmonicity_general_reserve
      X hnbv q hq W hW a x hxa
  exact hFactor.symm.trans hHarm
