-- Prove2me | solution 1 for Formalism.DivisionValues.W8.ph_nat_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:56.336136+00:00
-- url     : https://prove2.me/submissions/d2cb87cf-8fa9-42ce-974d-6aae11ee766f

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
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {La : ℝ} (r : ℕ) (h : Real.log (r : ℝ) ≤ La) : ph (r : ℝ) ≤ (r : ℝ) * La := by
  show (r : ℝ) * Real.log r - r ≤ r * La
  have h0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 := mul_le_mul_of_nonneg_left h h0
  linarith
end Formalism.DivisionValues.W8
