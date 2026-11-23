-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_top_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:58.451655+00:00
-- url     : https://prove2.me/submissions/797c4d0f-6140-4d67-bae9-913af21254de

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_succ_top
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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (ht : c.top = true) :
    Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp) := by
  have hk := hc.hk
  have h := vand_succ_top (c.k - 2) (fun i => c.u de (i + 1))
  have h2 := prod_shift (c.k - 2) (fun i => c.u de i - c.u de (c.k - 2 + 1 + 1))
  have e : c.k - 2 + 1 = c.k - 1 := by omega
  have e2 : c.k - 1 + 1 = c.k := by omega
  rw [h2] at h
  rw [e, e2, u_last c de hc] at h
  rw [h]
  have e3 : c.ulast = -c.bp := by simp [Cfg.ulast, ht]
  simp only [e3, sub_neg_eq_add]
end Formalism.FourierDecayAlt.P.Sz4
