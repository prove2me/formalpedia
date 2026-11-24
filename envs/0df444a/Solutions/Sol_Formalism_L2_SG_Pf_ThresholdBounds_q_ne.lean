-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.q_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:27:32.763153+00:00
-- url     : https://prove2.me/submissions/1fc73f7b-02df-4199-83b0-711405ed4e19

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_qfac_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
namespace Formalism.L2.SG.Pf.ThresholdBounds
theorem _root_.solution (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de de' : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    (hw' : Sz.IsWord c.k de') {l : ℕ} (hl : l + 1 ≤ c.k) {T T' : ℝ} (hT : T ≠ 0) (hT' : T' ≠ 0) {Y : ℝ}
    (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) : c.q de de' T T' Y ≠ 0 := by
  show -(T * T') * ∏ i ∈ Icc 1 c.k, ((Y + 1 / 2 + c.u de i) * (Y + 1 / 2 + c.u de' i)) ≠ 0
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hT hT')) ?_
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact mul_ne_zero (qfac_ne c hOk hb1 hw hl hY1 hY2 hi.1 hi.2)
    (qfac_ne c hOk hb1 hw' hl hY1 hY2 hi.1 hi.2)
end Formalism.L2.SG.Pf.ThresholdBounds
