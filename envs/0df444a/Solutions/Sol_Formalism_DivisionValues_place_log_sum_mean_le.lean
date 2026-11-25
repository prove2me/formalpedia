-- Prove2me | solution 1 for Formalism.DivisionValues.place_log_sum.mean_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:33:38.993189+00:00
-- url     : https://prove2.me/submissions/caac3d71-b92a-469e-8640-a453b6956963

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundRows
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum

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
open Formalism.DivisionValues.place_log_sum
namespace Formalism.DivisionValues.place_log_sum
theorem _root_.solution {E : Type} [Fintype E] [Nonempty E] (u : E → ℝ) (B : ℝ) (h : ∀ s, u s ≤ B) :
    (∑ s, u s) / (Fintype.card E : ℝ) ≤ B := by
  have hc : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  calc ∑ s, u s ≤ ∑ _s : E, B := Finset.sum_le_sum fun s _ => h s
    _ = B * (Fintype.card E : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end Formalism.DivisionValues.place_log_sum
