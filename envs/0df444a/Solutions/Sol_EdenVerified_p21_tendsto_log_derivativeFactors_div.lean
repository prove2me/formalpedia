-- Prove2me | solution 1 for EdenVerified.p21_tendsto_log_derivativeFactors_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:31:56.928485+00:00
-- url     : https://prove2.me/submissions/b6b32354-4df0-473e-8867-121b72a03b6b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_log_derivativeFactors_div


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log (derivativeFactors c t p i) / t) atTop
      (𝓝 (factorExponents c p i)) :=
  @Eden.tendsto_log_derivativeFactors_div
end EdenVerified
