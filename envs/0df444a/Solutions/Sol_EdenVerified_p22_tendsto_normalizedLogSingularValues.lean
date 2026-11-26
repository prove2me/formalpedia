-- Prove2me | solution 1 for EdenVerified.p22_tendsto_normalizedLogSingularValues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:32:13.429182+00:00
-- url     : https://prove2.me/submissions/da824b84-cad2-4623-becb-3b6bd86c09fb

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendsto_normalizedLogSingularValues


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    Tendsto (fun t => normalizedLogSingularValues c t p) atTop
      (𝓝 (descending (factorExponents c p))) :=
  @Eden.tendsto_normalizedLogSingularValues
end EdenVerified
