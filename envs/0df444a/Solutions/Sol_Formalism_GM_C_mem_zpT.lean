-- Prove2me | solution 1 for Formalism.GM.C_mem_zpT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:26.064797+00:00
-- url     : https://prove2.me/submissions/f41d9e36-7ea5-4254-b70b-b85e448fc82d

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial
namespace Formalism.GM
theorem _root_.solution (p : ℕ) [Fact p.Prime] {a : ℚ} (ha : a ∈ zpS p) : C a ∈ zpT p := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact Subring.zero_mem _
end Formalism.GM
