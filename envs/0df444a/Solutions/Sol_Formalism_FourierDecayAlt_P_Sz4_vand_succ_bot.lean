-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.vand_succ_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:31.188808+00:00
-- url     : https://prove2.me/submissions/c905ef00-74ad-4b85-b63a-c68b67a8ee7b

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_shift_Ioc

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
theorem _root_.solution (p : ℕ) (x : ℕ → ℝ) :
    Vand (p + 1) x = (∏ j ∈ Icc 2 (p + 1), (x 1 - x j)) * Vand p (fun i => x (i + 1)) := by
  unfold Vand
  have h1 : Icc 1 (p + 1) = insert 1 (Icc 2 (p + 1)) := by
    ext a; simp only [mem_Icc, mem_insert]; omega
  have h2 : Ioc 1 (p + 1) = Icc 2 (p + 1) := by
    ext a; simp only [mem_Icc, mem_Ioc]; omega
  rw [h1, Finset.prod_insert (by simp), h2]
  congr 1
  rw [← prod_shift p (fun i => ∏ j ∈ Ioc i (p + 1), (x i - x j))]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (prod_shift_Ioc i p (fun j => x (i + 1) - x j)).symm
end Formalism.FourierDecayAlt.P.Sz4
