-- Prove2me | solution 1 for Formalism.DivisionValues.W8.arith_fact_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:01.724936+00:00
-- url     : https://prove2.me/submissions/047341fc-fec1-4f0a-9ebc-66b0ace4dc6c

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
theorem _root_.solution {w S Sc N Bl cs C0 La n k : ℝ} (hw : 0 ≤ w) (hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hk : k = n + 2) (hkN : k ≤ N) (hcs : 0 ≤ cs) (hC2 : 2 ≤ C0) (hCcs : cs + 1 ≤ C0)
    (hSc : 2 * Sc ≤ C0 * S) (hLa : 1 ≤ La) :
    (2 * w + Sc + n * (cs * N) + Bl) * La + 1 ≤ C0 * (w + S + N ^ 2 + Bl) * La := by
  have hN : 2 ≤ N := by linarith
  have hnN := arith_nN hn (by linarith : n ≤ k) hkN hcs
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hC2 hw
  have h2 := mul_le_mul_of_nonneg_right hCcs (sq_nonneg N)
  have h3 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hBl
  have hin : 2 * w + Sc + n * (cs * N) + Bl + N ^ 2 ≤ C0 * (w + S + N ^ 2 + Bl) := by
    linarith
  have hLa0 : 0 ≤ La := by linarith
  have h4 := mul_le_mul_of_nonneg_right hin hLa0
  have h5 := mul_le_mul_of_nonneg_left hLa (sq_nonneg N)
  nlinarith
end Formalism.DivisionValues.W8
