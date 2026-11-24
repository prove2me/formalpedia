-- Prove2me | solution 1 for Formalism.ZF.rso_Fy_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:32.463121+00:00
-- url     : https://prove2.me/submissions/0de1ea73-b13c-4ccf-9fdb-1026e8817316

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectShiftOf
import Theorems.Thm_Formalism_ZF_rso_deriv_zeta_diff

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
theorem _root_.solution (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1)
    (hz : riemannZeta w ≠ 0) : DifferentiableAt ℂ (Fy y) w := by
  have hd1 : DifferentiableAt ℂ (deriv riemannZeta) w :=
    rso_deriv_zeta_diff.differentiableAt (isOpen_ne.mem_nhds h1)
  have hd2 : DifferentiableAt ℂ riemannZeta w := differentiableAt_riemannZeta h1
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hd3 : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) w :=
    (differentiableAt_id).const_cpow (Or.inl hy0)
  have hden : w * (w - 1) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.2 h1)
  unfold Fy
  exact (((hd1.div hd2 hz).neg).mul hd3).div (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hden
end Formalism.ZF
