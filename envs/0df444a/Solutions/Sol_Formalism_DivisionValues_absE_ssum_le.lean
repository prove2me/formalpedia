-- Prove2me | solution 1 for Formalism.DivisionValues.absE_ssum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:42.528398+00:00
-- url     : https://prove2.me/submissions/5c988fe6-6825-46f3-8d58-01ce5fc61661

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AbsorbE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution {J : Type} [Fintype J] (g : J → ℝ) (c m : ℝ)
    (hJ : (Fintype.card J : ℝ) = m) (hg : ∀ j, g j ≤ c) : ∑ j, g j ≤ m * c := by
  calc ∑ j, g j ≤ ∑ _j : J, c := Finset.sum_le_sum (fun j _ => hg j)
    _ = m * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hJ]
end Formalism.DivisionValues
