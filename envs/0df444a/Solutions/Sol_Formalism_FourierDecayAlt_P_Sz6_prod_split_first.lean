-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.prod_split_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:31.889804+00:00
-- url     : https://prove2.me/submissions/0fcffe62-a50b-43aa-a2c5-ecd6fe03f1e8

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_Icc_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6
namespace Formalism.FourierDecayAlt.P.Sz6
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ) :
    ∏ i ∈ Icc 1 k, F i = F 1 * ∏ i ∈ Icc 1 (k - 1), F (i + 1) := by
  have e2 : Icc 1 (k - 1) = Ico 1 k := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [Icc_one_eq, e2, prod_eq_prod_Ico_succ_bot (by omega), prod_Ico_add' F 1 k 1]
end Formalism.FourierDecayAlt.P.Sz6
