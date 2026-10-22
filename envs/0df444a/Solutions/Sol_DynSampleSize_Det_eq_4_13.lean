-- Prove2me | solution 1 for DynSampleSize.Det.eq_4_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:29:54.638267+00:00
-- url     : https://prove2.me/submissions/68a4caef-e4b2-4476-916e-ff2e42af1b28

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting
set_option autoImplicit false
open Filter Topology

theorem solution {m : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (g v : EuclideanSpace ℝ (Fin m)) (h48 : ‖g - v‖ ≤ θ * ‖g‖) :
    ‖v‖ ≤ (1 + θ) * ‖g‖ ∧ (1 - θ) * ‖g‖ ≤ ‖v‖ := by
  have h := abs_norm_sub_norm_le g v
  have h' := abs_le.mp (h.trans h48)
  constructor <;> linarith [h'.1, h'.2]
