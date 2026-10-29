-- Prove2me | solution 8 for AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:04:06.304523+00:00
-- url     : https://prove2.me/submissions/65d210dc-1840-41ac-a5e8-595b9f51dc83
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_lintegral_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_expectation_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

-- Repair of CE 18021 (E01-E04): the failed source applied bare
-- `lintegral_congr (fun ω => ...)` with no expected type, leaving the
-- measure μ, the measurable-space instance m, and the integrands f g as
-- unsynthesized metavariables (E01/E02), so the `have` itself failed to
-- elaborate (E03) and the rewrite chain never closed the goal (E04).
-- Fix: ascribe the full integral-equation type to hEq. The expected type
-- pins μ := P, m := mΩ, and both integrands; the pointwise proof then
-- elaborates against `∀ ω, f ω = g ω` with f and g known. All helper names,
-- binder orders and imports are unchanged from 18021 (all verified at the
-- pinned revision: 3a6690c2 and e1242e81 Proved, 322217fe Open and
-- decomposition-sanctioned with an acyclic route, so expect SKETCH_ACCEPTED).
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by
  have hEq : (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
    else 0 ∂P) :=
    lintegral_congr (fun ω =>
      (AvramDividend.Classical.chat04_strict_upper_exit_scale_payoff
        X W q a x hxa ω).symm)
  have hFac :=
    AvramDividend.Classical.chat04_strict_stopped_exit_payoff_lintegral_factorisation
      X q a x hxa W
  have hOST :=
    AvramDividend.Classical.bv_stopped_scale_ost_expectation_identity
      X hX q hq W hW hBV a x ha hx0 hxa
  rw [hEq, hFac]
  exact hOST
