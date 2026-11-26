-- Prove2me | solution 1 for EdenVerified.p22_tendsto_lyapunovExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:13.919916+00:00
-- url     : https://prove2.me/submissions/50c9a489-56a8-4123-8e7f-71df7104ef1c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_lyapunovExponent


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) :=
  @Eden.tendsto_lyapunovExponent
end EdenVerified
