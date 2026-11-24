-- Prove2me | solution 1 for Formalism.GM.M.lv_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:57.296271+00:00
-- url     : https://prove2.me/submissions/0c1e2dc3-2320-4ec7-ab84-95d8ff7a00b5

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_lv_castSucc
import Theorems.Thm_Formalism_GM_M_lv_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {t : ℕ}
namespace Formalism.GM.M
theorem _root_.solution {j j' : Fin t → ℕ} {jp jp' : ℕ} (h : lv j jp = lv j' jp') : j = j' ∧ jp = jp' := by
  refine ⟨funext fun k => ?_, ?_⟩
  · rw [← lv_castSucc j jp k, h, lv_castSucc]
  · rw [← lv_last j jp, h, lv_last]
end Formalism.GM.M
