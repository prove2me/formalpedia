-- Prove2me | solution 1 for Formalism.deriv_riemannZetaOne_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:30.918953+00:00
-- url     : https://prove2.me/submissions/4a84ea25-c023-46c2-9478-7198799b6f16

import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
import Theorems.Thm_Formalism_riemannZetaOne_eq_mul_of_ne_one

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
theorem _root_.solution {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : riemannZeta₁ =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact riemannZetaOne_eq_mul_of_ne_one hz
  rw [heq.deriv_eq]
  have h : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
    ((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  rw [h.deriv]
  ring
end Formalism
