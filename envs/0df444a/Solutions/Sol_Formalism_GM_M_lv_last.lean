-- Prove2me | solution 1 for Formalism.GM.M.lv_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:03.370802+00:00
-- url     : https://prove2.me/submissions/709d1847-aac3-4dc5-8545-bb4f516d483b

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
theorem _root_.solution (j : Fin t → ℕ) (jp : ℕ) : lv j jp (Fin.last t) = jp := by
  simp [lv, Finset.sum_apply, Pi.single_apply, (Fin.castSucc_ne_last _).symm]
end Formalism.GM.M
