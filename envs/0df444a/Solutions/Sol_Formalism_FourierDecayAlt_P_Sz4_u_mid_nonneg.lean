-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.u_mid_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:37.286551+00:00
-- url     : https://prove2.me/submissions/51fd7350-5a19-4e2d-a07f-ed5bb0dfb8a2

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid

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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ)
    (hi : i ∈ Icc 2 (c.k - 1)) : 0 ≤ c.u de i := by
  rw [u_mid c de hw i hi]
  rw [mem_Icc] at hi
  have hD := hc.hDel
  have hv0 := hc.hv0
  have hiR : ((i - 1 : ℕ) : ℝ) + 2 ≤ c.k := by exact_mod_cast (by omega : i - 1 + 2 ≤ c.k)
  have m : 0 ≤ c.Del * ((c.k : ℝ) - 2 - ((i - 1 : ℕ) : ℝ)) := mul_nonneg (by linarith) (by linarith)
  unfold Cfg.v
  rcases hw.1 (i - 1) with e | e <;> rw [e] <;> nlinarith
end Formalism.FourierDecayAlt.P.Sz4
