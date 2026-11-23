-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz6.prob_and_eq_mul_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:31.898605+00:00
-- url     : https://prove2.me/submissions/5c8b45e2-fc0d-4119-80fa-61a296cad802

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
theorem _root_.solution (c : Cfg) (hk : 1 ≤ c.k) (Y : ℝ) :
    c.P Y = (∏ i ∈ Icc 1 (c.k - 1), (Y + c.v i)) * ∏ j ∈ Icc 1 c.m, (Y - c.b j) := by
  have e1 : Icc 1 (c.k + c.m - 1) = Ico 1 (c.k + c.m) := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  have e2 : Icc 1 (c.k - 1) = Ico 1 c.k := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  unfold Cfg.P
  rw [e1, e2, Icc_one_eq, ← prod_Ico_consecutive _ hk (Nat.le_add_right c.k c.m)]
  congr 1
  · apply prod_congr rfl
    intro i hi
    rw [mem_Ico] at hi
    simp only [Cfg.lam, if_pos hi.2]
  · rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
    have a1 : c.k + c.m - c.k = c.m := by omega
    have a2 : c.m + 1 - 1 = c.m := by omega
    rw [a1, a2]
    apply prod_congr rfl
    intro i _
    have n1 : ¬ (c.k + i < c.k) := by omega
    have n2 : c.k + i + 1 - c.k = 1 + i := by omega
    simp only [Cfg.lam, if_neg n1, n2]
    ring
end Formalism.FourierDecayAlt.P.Sz6
