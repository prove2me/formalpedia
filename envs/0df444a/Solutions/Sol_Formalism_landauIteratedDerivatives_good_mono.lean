-- Prove2me | solution 1 for Formalism.landauIteratedDerivatives.good_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:34.313868+00:00
-- url     : https://prove2.me/submissions/6c0377fb-c710-4211-95f7-9f3333e2642d

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LandauLemma
import Theorems.Thm_Formalism_landauIteratedDerivatives_meas_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open Formalism.landauIteratedDerivatives
namespace Formalism.landauIteratedDerivatives
theorem _root_.solution {H : ℝ → ℝ} (hH : AEStronglyMeasurable H (volume.restrict (Ioi 1)))
    {σ σ' : ℝ} (h : Good H σ) (hle : σ ≤ σ') : Good H σ' := by
  refine Integrable.mono h (meas_rpow H hH σ') ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
    (norm_nonneg _)
end Formalism.landauIteratedDerivatives
