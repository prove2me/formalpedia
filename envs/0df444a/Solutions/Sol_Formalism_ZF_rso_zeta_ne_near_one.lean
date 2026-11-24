-- Prove2me | solution 1 for Formalism.ZF.rso_zeta_ne_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:09.117013+00:00
-- url     : https://prove2.me/submissions/e563d016-0cb2-4275-892e-b250c9ee6a59

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : ∀ᶠ w in 𝓝 (1 : ℂ), w ≠ 1 → riemannZeta w ≠ 0 := by
  have h := riemannZeta_residue_one.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))
  rw [eventually_nhdsWithin_iff] at h
  filter_upwards [h] with w hw hw1 hz
  exact hw hw1 (by rw [hz, mul_zero])
end Formalism.ZF
