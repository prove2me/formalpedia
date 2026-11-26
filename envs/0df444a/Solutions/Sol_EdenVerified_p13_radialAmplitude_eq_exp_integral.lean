-- Prove2me | solution 1 for EdenVerified.p13_radialAmplitude_eq_exp_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:24:50.869252+00:00
-- url     : https://prove2.me/submissions/1c0a0d5b-7875-4079-b294-9e27fc7a0d3b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialAmplitude_eq_exp_integral


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) :=
  @Eden.radialAmplitude_eq_exp_integral
end EdenVerified
