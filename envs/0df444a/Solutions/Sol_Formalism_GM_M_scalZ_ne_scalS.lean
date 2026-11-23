-- Prove2me | solution 1 for Formalism.GM.M.scalZ_ne_scalS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:27.064516+00:00
-- url     : https://prove2.me/submissions/2511b196-d8d3-4890-b12b-7b95c16c8d90

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
theorem _root_.solution (i k : Fin (t + 1)) : scalZ N r t i ≠ scalS N r t k := by simp [scalZ, scalS]
end Formalism.GM.M
