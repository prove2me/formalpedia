-- Prove2me | solution 1 for Formalism.GM.M.inl_ne_scalS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:06.47736+00:00
-- url     : https://prove2.me/submissions/1e6cc0b4-9604-4b09-9902-e24be361f207

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
theorem _root_.solution (x : Fin (N + 1) × Fin r) (k : Fin (t + 1)) : (Sum.inl x : BVar N r t) ≠ scalS N r t k := by
  simp [scalS]
end Formalism.GM.M
