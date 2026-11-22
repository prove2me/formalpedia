-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.u_mid
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:30.319563+00:00
-- url     : https://prove2.me/submissions/c1dc79a2-2c3d-4a91-9170-c5a5a5c07ec0

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_succ

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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : i ∈ Icc 2 (c.k - 1)) :
    c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by
  rw [mem_Icc] at hi
  have := u_succ c de hw (i - 1) (by omega) (by omega) (Or.inl (by omega))
  rwa [Nat.sub_add_cancel (by omega)] at this
end Formalism.FourierDecayAlt.P.Sz4
