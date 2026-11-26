-- Prove2me | solution 1 for EdenVerified.p22_normalizedLogSingularValues_eq_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:32:02.424294+00:00
-- url     : https://prove2.me/submissions/86a2d025-77f8-4e25-a83a-eecf7bc3e06d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_normalizedLogSingularValues_eq_descending


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace),
    normalizedLogSingularValues c t p =
      descending (fun i => Real.log (derivativeFactors c t p i) / t) :=
  @Eden.normalizedLogSingularValues_eq_descending
end EdenVerified
