-- Prove2me | solution 1 for Formalism.DivisionValues.W8.ph_nat_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:06:08.067467+00:00
-- url     : https://prove2.me/submissions/ac9e42b5-9bdd-4260-9a8b-82d4a482f237

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
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
theorem _root_.solution (y y' : ℕ) (h : y < y') : ph (y : ℝ) - ph (y' : ℝ) ≤ 1 := by
  have hlt : (y : ℝ) < y' := by exact_mod_cast h
  have hy'pos : (0 : ℝ) < y' := lt_of_le_of_lt (Nat.cast_nonneg y) hlt
  rcases Nat.eq_zero_or_pos y with h0 | h0
  · subst h0
    have hne : (y' : ℝ) ≠ 0 := hy'pos.ne'
    have hl := Real.one_sub_inv_le_log_of_pos hy'pos
    have e : (y' : ℝ) * (1 - (y' : ℝ)⁻¹) = y' - 1 := by
      rw [mul_sub, mul_one, mul_inv_cancel₀ hne]
    have h2 := mul_le_mul_of_nonneg_left hl hy'pos.le
    simp only [ph, Nat.cast_zero, Real.log_zero, mul_zero, sub_zero, zero_sub]
    linarith
  · have hu : (0 : ℝ) < y := by exact_mod_cast h0
    have ht := ph_sub_ph_le_mul_log hu (Nat.cast_nonneg (α := ℝ) y')
    have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr h0)
    have h3 : ((y : ℝ) - y') * Real.log y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog0
    linarith
end Formalism.DivisionValues.W8
