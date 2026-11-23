-- Prove2me | solution 1 for Formalism.DivisionValues.W8.sum_ph_le_logFact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:13.089564+00:00
-- url     : https://prove2.me/submissions/f5871e26-d037-4559-bec0-be6ac3208943

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_W8_logFactRows_add
import Theorems.Thm_Formalism_DivisionValues_W8_logFactRows_univ
import Theorems.Thm_Formalism_DivisionValues_W8_logFactRows_nonneg
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
private lemma ph_natCast_le_log_factorial (n : ℕ) : ph (n : ℝ) ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    simp [ph]
  · have hn : (0 : ℝ) < n := by exact_mod_cast h0
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have h1 := Real.pow_div_factorial_le_exp (n : ℝ) hn.le n
    have h2 : Real.log ((n : ℝ) ^ n / n.factorial) ≤ n := by
      have := Real.log_le_log (div_pos (pow_pos hn n) hf) h1
      rwa [Real.log_exp] at this
    rw [Real.log_div (pow_pos hn n).ne' hf.ne', Real.log_pow] at h2
    show (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ)
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
theorem _root_.solution {n : ℕ} (r : Fin n → ℕ) (sm : Multiset ℕ) :
    ∑ i, ph (r i : ℝ) ≤ logFactRows (Finset.univ.val.map r + sm) := by
  rw [logFactRows_add, logFactRows_univ]
  have h0 := logFactRows_nonneg sm
  have h : ∑ i, ph (r i : ℝ) ≤ ∑ i, Real.log ((r i).factorial : ℝ) :=
    Finset.sum_le_sum fun i _ => ph_natCast_le_log_factorial (r i)
  linarith
end Formalism.DivisionValues.W8
