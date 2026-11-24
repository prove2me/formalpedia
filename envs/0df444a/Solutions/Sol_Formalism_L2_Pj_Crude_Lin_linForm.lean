-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.Lin_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:20.564504+00:00
-- url     : https://prove2.me/submissions/ba409560-4a62-4e61-9c5c-82d67b8d7722

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (b b' : Fin n) (v w : Fin d → k) :
    Lin b v (∑ j : Fin d, C (w j) * (X (b', j) : PS k n d)) =
      C (if b = b' then ∑ j : Fin d, v j * w j else 0) := by
  unfold Lin
  by_cases h : b = b'
  · subst h
    simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Finset.mul_sum,
      map_sum, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Pi.single_apply,
      Prod.ext_iff, h]
end Formalism.L2.Pj.Crude
