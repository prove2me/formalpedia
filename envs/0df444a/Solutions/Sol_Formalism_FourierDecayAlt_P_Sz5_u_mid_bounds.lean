-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.u_mid_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:38.515876+00:00
-- url     : https://prove2.me/submissions/a8509eaf-821a-4cd2-9ead-62e3d8a72e4b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (c : Cfg) (h : c.Ok) (de : ℕ → ℝ) (hw : IsWord c.k de) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j + 2 ≤ c.k) : 0 ≤ c.u de (j + 1) ∧ c.u de (j + 1) ≤ c.v 1 := by
  rw [u_mid c de j h1 h2]
  have hj : (j:ℝ) + 2 ≤ (c.k:ℝ) := by exact_mod_cast h2
  have hj1 : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast h1
  have hD := h.hDel
  have hv0 := h.hv0
  rcases hw.1 j with hd | hd <;> rw [hd] <;> simp only [Cfg.v, Nat.cast_one] <;>
    constructor <;> nlinarith
end Formalism.FourierDecayAlt.P.Sz5
