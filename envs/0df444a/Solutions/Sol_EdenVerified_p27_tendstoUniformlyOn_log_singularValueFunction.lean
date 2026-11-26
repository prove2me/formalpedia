-- Prove2me | solution 1 for EdenVerified.p27_tendstoUniformlyOn_log_singularValueFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:50.959795+00:00
-- url     : https://prove2.me/submissions/115abcfd-38ea-4632-a734-9db12e211027

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tendstoUniformlyOn_log_singularValueFunction


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) (p : PhaseSpace),
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) :=
  @Eden.tendstoUniformlyOn_log_singularValueFunction
end EdenVerified
