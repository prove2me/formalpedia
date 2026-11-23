-- Prove2me | solution 1 for Formalism.DivisionValues.W8.arith_fact_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:00.600358+00:00
-- url     : https://prove2.me/submissions/2aea8ab5-4d02-4012-bbd6-ebe44c50c455

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook
import Theorems.Thm_Formalism_DivisionValues_W8_arith_nN

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
open W8
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {w S Sc N Bl cs C0 La n k : ℝ} (hw : 0 ≤ w) (_hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hk : k = n + 1) (hkN : k ≤ N) (hcs : 0 ≤ cs) (hC2 : 2 ≤ C0) (hCcs : cs + 1 ≤ C0)
    (hSc : 2 * Sc ≤ C0 * S) (hLa : 1 ≤ La) :
    (w + 2 * Sc + n * (cs * N) + Bl) * La ≤ C0 * (w + S + N ^ 2 + Bl) * La := by
  have hnN := arith_nN hn (by linarith : n ≤ k) hkN hcs
  have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
  have h1 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hw
  have h2 := mul_le_mul_of_nonneg_right (by linarith : cs ≤ C0) hN2
  have h3 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hBl
  have hin : w + 2 * Sc + n * (cs * N) + Bl ≤ C0 * (w + S + N ^ 2 + Bl) := by
    linarith
  exact mul_le_mul_of_nonneg_right hin (by linarith)
end Formalism.DivisionValues.W8
