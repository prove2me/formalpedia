-- Prove2me | solution 1 for Formalism.DivisionValues.W8.pair_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:24:33.05794+00:00
-- url     : https://prove2.me/submissions/aeac3c86-1f03-495d-bb35-a89bf970302e

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_W8_ph_nat_lt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
namespace W8
private lemma ph_sub_ph_le_mul_log {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    ph u - ph v ≤ (u - v) * Real.log u := by
  show u * Real.log u - u - (v * Real.log v - v) ≤ (u - v) * Real.log u
  have key : v * (Real.log u - Real.log v) ≤ u - v := by
    rcases hv.lt_or_eq with hv' | hv'
    · have hne : v ≠ 0 := hv'.ne'
      have h1 := Real.log_le_sub_one_of_pos (div_pos hu hv')
      rw [Real.log_div hu.ne' hne] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hv
      have h3 : v * (u / v) = u := by
        rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hne, mul_one]
      have h4 : v * (u / v - 1) = v * (u / v) - v := by ring
      linarith
    · subst hv'
      simp only [zero_mul, sub_zero]
      exact hu.le
  linarith
end W8
open W8
namespace W8
end W8
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {La d : ℝ} (y y' : ℕ) (hy : Real.log (y : ℝ) ≤ La) (hLa : 1 ≤ La) (hd0 : 0 ≤ d)
    (hd : (y : ℝ) - (y' : ℝ) ≤ d) : ph (y : ℝ) - ph (y' : ℝ) ≤ d * La + 1 := by
  have hLa0 : 0 ≤ La := by linarith
  have hdL : 0 ≤ d * La := mul_nonneg hd0 hLa0
  rcases lt_or_ge y y' with hlt | hle
  · have := ph_nat_lt y y' hlt
    linarith
  · rcases Nat.eq_zero_or_pos y with h0 | h0
    · have hyy : y = y' := by omega
      rw [hyy, sub_self]
      linarith
    · have hu : (0 : ℝ) < y := by exact_mod_cast h0
      have ht := ph_sub_ph_le_mul_log hu (Nat.cast_nonneg (α := ℝ) y')
      have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr h0)
      have h1 : ((y : ℝ) - y') * Real.log y ≤ d * Real.log y := mul_le_mul_of_nonneg_right hd hlog0
      have h2 : d * Real.log y ≤ d * La := mul_le_mul_of_nonneg_left hy hd0
      linarith
end Formalism.DivisionValues.W8
