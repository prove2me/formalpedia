-- Prove2me | solution 1 for CohnElkies.tendsto_upperGammaEuler_log_norm_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/bca716ee-1ff2-443e-8c51-91146a827a92

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {m : ℝ} (hm : 0 < m) (b : ℝ) :
    Tendsto
      (fun n : ℕ =>
        Real.log
          (‖Complex.GammaSeq
              ((m : ℂ) + Complex.I * (b : ℂ)) n‖ /
            ‖Complex.GammaSeq (m : ℂ) n‖))
      atTop
      (𝓝
        (Real.log
          (‖Complex.Gamma
              ((m : ℂ) + Complex.I * (b : ℂ))‖ /
            ‖Complex.Gamma (m : ℂ)‖))) := by
  let z : ℂ := (m : ℂ) + Complex.I * (b : ℂ)
  have hzre : 0 < z.re := by simpa [z] using! hm
  have hnum : ‖Complex.Gamma z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos hzre)
  have hden : ‖Complex.Gamma (m : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos
        (by simpa using! hm))
  have hratio :=
    (Complex.GammaSeq_tendsto_Gamma z).norm.div
      (Complex.GammaSeq_tendsto_Gamma (m : ℂ)).norm
      hden
  exact hratio.log (div_ne_zero hnum hden)
end CohnElkies
