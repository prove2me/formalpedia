-- Prove2me | solution 1 for Formalism.DivisionValues.prime_log_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:44.648802+00:00
-- url     : https://prove2.me/submissions/6157b259-d0f8-482e-98a7-3b4dd474c783

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Theorems.Thm_Formalism_LogFactorialBounds_sum_primesLE_log_div_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : PrimeLogSum := by
  intro Y hY s hs
  have hn : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hnR : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  calc ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ Real.log (⌊Y⌋₊ : ℝ) + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hn
    _ ≤ Real.log Y + Real.log 4 := by
        have := Real.log_le_log hnR hfl
        linarith
end Formalism.DivisionValues
