-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_u_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:39.351788+00:00
-- url     : https://prove2.me/submissions/23c79c91-a9c6-42f2-99fe-426ed94cae09

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_succ_bot
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_last

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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) :
    Vand c.k (c.u de) = (∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) * (c.a - c.ulast) *
      Vand (c.k - 1) (fun i => c.u de (i + 1)) := by
  have hk := hc.hk
  have h := vand_succ_bot (c.k - 1) (c.u de)
  have h2 := Finset.prod_Icc_succ_top (a := 2) (b := c.k - 1) (by omega)
    (fun j => c.u de 1 - c.u de j)
  rw [h2] at h
  rw [Nat.sub_add_cancel (by omega)] at h
  have h1 : c.u de 1 = c.a := by simp [Cfg.u]
  rw [h, h1, u_last c de hc]
end Formalism.FourierDecayAlt.P.Sz4
