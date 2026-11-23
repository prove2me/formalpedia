-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.position_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:40.700023+00:00
-- url     : https://prove2.me/submissions/fab31a2b-ef7d-43a5-96f0-3a8bb4ba8308

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_v_sub
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
theorem _root_.solution (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i < j) (hj : j + 1 ≤ c.k) (h : j + 2 ≤ c.k ∨ c.top = false) :
    c.u de (i + 1) - c.u de (j + 1) =
      (1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) * (c.v i - c.v j) := by
  rw [u_succ c de hw i hi (by omega) (Or.inl (by omega)), u_succ c de hw j (by omega) hj h, v_sub]
  have hpos : (0 : ℝ) < (j : ℝ) - i := by
    have : (i : ℝ) < j := by exact_mod_cast hij
    linarith
  have h3 := v_sub c i j
  field_simp
  linarith
end Formalism.FourierDecayAlt.P.Sz4
