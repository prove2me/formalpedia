-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:09.60781+00:00
-- url     : https://prove2.me/submissions/eae34142-ed23-4e79-b4ec-3abee7522d49

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP
namespace Formalism.G0.TailConcavityP
theorem _root_.solution (a b i : ℕ) :
    Real.log ((a : ℝ) + i + 1) - Real.log ((b : ℝ) + i + 1) ≤
      1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by
  have hb : (0 : ℝ) < b + i + 1 := by positivity
  have ha : (0 : ℝ) < a + i + 1 := by positivity
  rw [← Real.log_div ha.ne' hb.ne']
  have h1 := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have e : ((a : ℝ) + i + 1) / (b + i + 1) - 1 = 1 / ((b : ℝ) + i + 1) * ((a : ℝ) - b) := by
    field_simp
    ring
  linarith
end Formalism.G0.TailConcavityP
