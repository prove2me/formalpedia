-- Prove2me | solution 1 for Formalism.DivisionValues.W8.arith_per
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:01.446876+00:00
-- url     : https://prove2.me/submissions/273943e5-21c4-4100-86bb-df67b7cf1831

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
open W8
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {d w S Sc N Bl C0 n k X : ℝ} (hw : 0 ≤ w) (hSc0 : 0 ≤ Sc) (hBl : 0 ≤ Bl)
    (hn : 0 ≤ n) (hnk : n ≤ k) (hkN : k ≤ N) (hC2 : 2 ≤ C0) (hSc : 2 * Sc ≤ C0 * S) (hX : 0 ≤ X)
    (h1 : -w ≤ d) (h2 : d ≤ n * Sc + Bl) :
    |d| ≤ C0 * (w + k * (N + S) + Bl + X) := by
  have hk0 : 0 ≤ k := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hCS : 0 ≤ C0 * S := by linarith
  have hC0 : 0 ≤ C0 := by linarith
  have e1 := mul_le_mul_of_nonneg_right hnk hSc0
  have e2 := mul_le_mul_of_nonneg_left hSc hk0
  have e3 := mul_nonneg (mul_nonneg hC0 hk0) hN0
  have e4 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hw
  have e5 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C0) hBl
  have e6 := mul_nonneg hC0 hX
  have e7 := mul_nonneg hk0 hCS
  rw [abs_le]
  constructor <;> nlinarith
end Formalism.DivisionValues.W8
