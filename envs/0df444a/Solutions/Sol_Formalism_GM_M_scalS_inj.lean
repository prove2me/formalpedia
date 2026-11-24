-- Prove2me | solution 1 for Formalism.GM.M.scalS_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:03.429168+00:00
-- url     : https://prove2.me/submissions/ea34f072-48a7-4509-b9b6-bda88419ba50

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
theorem _root_.solution : Function.Injective (scalS N r t) := by
  intro a b h; simpa [scalS] using h
end Formalism.GM.M
