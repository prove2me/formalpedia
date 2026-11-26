-- Prove2me | solution 1 for EdenVerified.p13_log_planarAmplitude_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:24:23.442455+00:00
-- url     : https://prove2.me/submissions/69a02db2-256a-43e6-8350-229f3f64d69a

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_log_planarAmplitude_eq_integral


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (planarAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s) :=
  @Eden.log_planarAmplitude_eq_integral
end EdenVerified
