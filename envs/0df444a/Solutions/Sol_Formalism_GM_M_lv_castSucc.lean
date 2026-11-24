-- Prove2me | solution 1 for Formalism.GM.M.lv_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:03.316052+00:00
-- url     : https://prove2.me/submissions/5cf28c6c-11f4-4b95-9964-ff3c43ca63fe

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

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
theorem _root_.solution (j : Fin t → ℕ) (jp : ℕ) (k : Fin t) : lv j jp (Fin.castSucc k) = j k := by
  simp [lv, Finset.sum_apply, Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last]
end Formalism.GM.M
