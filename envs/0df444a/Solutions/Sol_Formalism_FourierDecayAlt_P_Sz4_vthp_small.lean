-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vthp_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:15.113491+00:00
-- url     : https://prove2.me/submissions/38b9d7b1-1590-4725-bab6-621512b7642b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_bp_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (hc : c.Ok) (hv : c.vth ≤ 1 / 10) (ht : c.top = true) :
    c.vthp ≤ 1 / 10 := by
  have hb := bp_pos c hc ht
  have hb1 := hc.hb1
  have hbb := (hc.htop ht).1
  have hm : (2 : ℝ) ≤ c.m := by exact_mod_cast hc.hm
  have hkD := kDel_pos c hc
  have e : c.vthp = 4 * c.k * c.Del / c.bp := by simp [Cfg.vthp, ht]
  unfold Cfg.vth at hv
  rw [div_le_iff₀ (by linarith)] at hv
  rw [e, div_le_iff₀ hb]
  have : 2 * (4 * (c.k : ℝ) * c.Del) ≤ 4 * c.m * c.k * c.Del := by nlinarith
  linarith
end Formalism.FourierDecayAlt.P.Sz4
