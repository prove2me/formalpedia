-- Prove2me | solution 1 for Formalism.GM.bad_criterion_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:48.614806+00:00
-- url     : https://prove2.me/submissions/1d216352-5082-4b26-88ec-7347e5fc43f4

import Definitions.Def_Formalism_MahlerMeasure_StatementT
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Theorems.Thm_Formalism_GM_badCrit_goodCount_bdd
import Theorems.Thm_Formalism_GM_badCrit_pairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Module
namespace Formalism.GM
theorem _root_.solution : M.BadCrit := by
  intro p _ Vs _ _ _ _ be L L₁ D hfin hle _hsat hprim
  obtain ⟨x, y, hx, hy, hxy⟩ := badCrit_pairs be L L₁ D hle hprim
  have hg : Module.finrank ℤ_[p] L₁ ≤ M.goodCount p (fun x y => be x y) L D :=
    le_csSup (badCrit_goodCount_bdd be L D) ⟨x, y, hx, hy, hxy⟩
  unfold M.bad
  omega
end Formalism.GM
