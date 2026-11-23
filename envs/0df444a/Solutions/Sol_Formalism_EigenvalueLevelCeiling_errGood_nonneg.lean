-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.errGood_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:59.05344+00:00
-- url     : https://prove2.me/submissions/5c0b8887-acca-4169-9755-fbf087b383c1

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (hkw : 0 ≤ kw) (hT : 0 ≤ T) (hth : ∀ p, 0 ≤ th p) (hadd : ∀ p, 0 ≤ add p) (p : ℕ) :
    0 ≤ errGood Y X2 A1 A2 kw T th add p := by
  have hp : (0:ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have e1 : 0 ≤ A1 / (p : ℝ) := div_nonneg hA1 hp
  have e2 : 0 ≤ kw * th p := mul_nonneg hkw (hth p)
  have e3 : 0 ≤ T * add p := mul_nonneg hT (hadd p)
  have e4 : 0 ≤ A2 / (p : ℝ) ^ 2 := div_nonneg hA2 (by positivity)
  unfold errGood
  split_ifs <;> linarith
end Formalism.EigenvalueLevelCeiling
