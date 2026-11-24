-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.tail_line_c_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:32.556812+00:00
-- url     : https://prove2.me/submissions/ab692fc9-01d5-4a6b-81b1-8a1aa17452e8

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LogSmallConstantBounds_b_pos__c78f2de8288c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : ParameterQuotientBoundOfTwoLeF := by
  intro P H hf hL
  have ht := H.t_ge
  have hm := H.m_pos
  have hmk := H.m_le
  have hN := H.Nr_eq
  have ht6 : 6 ≤ P.t := by omega
  have hk : 1 ≤ P.k := by omega
  have hk3 : 1 ≤ P.k ^ 3 := Nat.one_le_pow _ _ hk
  have h12 : 12 ≤ P.t * P.f * P.k ^ 3 * P.m := by
    calc 12 = 6 * 2 * 1 * 1 := by norm_num
      _ ≤ P.t * P.f * P.k ^ 3 * P.m :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ht6 hf) hk3) hm
  refine ⟨ht6, h12, ?_⟩
  intro η' h0 h3
  have hb : 0 < P.b := LogSmallConstantBounds.b_pos' P
  have htR : (0 : ℝ) < (P.t : ℝ) := by exact_mod_cast (by omega : 0 < P.t)
  have hfR : (0 : ℝ) < (P.f : ℝ) := by exact_mod_cast (by omega : 0 < P.f)
  have hkR : (0 : ℝ) < (P.k : ℝ) := by exact_mod_cast (by omega : 0 < P.k)
  have hNr : (P.Nr : ℝ) ≤ 2 * (P.t : ℝ) := by exact_mod_cast (by omega : P.Nr ≤ 2 * P.t)
  have hNr0 : (0 : ℝ) ≤ (P.Nr : ℝ) := Nat.cast_nonneg _
  have hD : 0 < (P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hL
    have hsq : (P.Nr : ℝ) ^ 2 ≤ 4 * (P.t : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul h3 hsq (by positivity) (by linarith)
  · have hη := H.η_le
    have e : 12 * P.L * P.b / ((P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3) =
        3 * (P.b / ((P.t : ℝ) ^ 3 * (P.f : ℝ) * (P.k : ℝ) ^ 3)) * (4 * (P.t : ℝ) ^ 2) * P.L := by
      field_simp
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hL
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith
  · rw [div_le_iff₀ hD]
    have h12R : (12 : ℝ) ≤ (P.t : ℝ) * (P.f : ℝ) * (P.k : ℝ) ^ 3 * (P.m : ℝ) := by
      exact_mod_cast h12
    have hLb : 0 ≤ P.L * P.b := mul_nonneg hL hb.le
    nlinarith [mul_le_mul_of_nonneg_left h12R hLb]
end Formalism.CohomologicalDescent.WorkedExample
