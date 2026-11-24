-- Prove2me | solution 1 for Formalism.logderiv_zeta_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:00:16.221131+00:00
-- url     : https://prove2.me/submissions/c73ae6a0-52af-4d47-b7d5-c6563f544211

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
import Theorems.Thm_Formalism_riemannZetaOne_eq_mul_of_ne_one
import Theorems.Thm_Formalism_deriv_riemannZetaOne_of_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      -(deriv riemannZeta₁ s / riemannZeta₁ s) + 1 / (s - 1) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZetaOne_of_ne_one hs, riemannZetaOne_eq_mul_of_ne_one hs]
  field_simp
  ring
end Formalism
