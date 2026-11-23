-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.a_sub_u_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:01.288828+00:00
-- url     : https://prove2.me/submissions/b70f0e75-3a21-4ca1-ba44-311c54613b39

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_edge_factor

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
    (hi : i ∈ Icc 2 (c.k - 1)) : 4 * c.k * c.Del ≤ c.a - c.u de i := by
  rw [mem_Icc] at hi
  have := (edge_factor c de hc hw i hi.1 (by omega) (Or.inl (by omega))).1
  linarith [hc.ha]
end Formalism.FourierDecayAlt.P.Sz4
