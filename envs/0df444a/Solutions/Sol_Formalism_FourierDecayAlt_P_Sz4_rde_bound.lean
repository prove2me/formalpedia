-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.rde_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:14.980801+00:00
-- url     : https://prove2.me/submissions/c1488861-27da-4229-99e3-569691f1c756

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_one_add_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_lin_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_quad_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_pair_small

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
theorem _root_.solution (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    Real.exp (-(((J : ℝ) + 1) / 4)) ≤ Rde J de ∧ Rde J de ≤ Real.exp (((J : ℝ) + 1) / 4) := by
  have hlin := abs_le.mp (lin_bound J hJ de h01)
  have hquad := quad_bound J de h01
  have hlog2 := Real.log_two_lt_d9
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · calc Real.exp (-(((J : ℝ) + 1) / 4))
        ≤ Real.exp (∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J,
            ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ))) -
              2 / 3 * ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
          nlinarith [hlin.1]
      _ = ∏ i ∈ Icc 1 J, ∏ j ∈ Ioc i J, Real.exp
            ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ))) -
              2 / 3 * ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) ^ 2) := by
          rw [Real.exp_sum]
          exact Finset.prod_congr rfl fun i _ => Real.exp_sum _ _
      _ ≤ Rde J de := by
          unfold Rde
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
            fun i _ => ?_
          refine Finset.prod_le_prod (fun j _ => (Real.exp_pos _).le) fun j hj => ?_
          exact one_add_ge _ (pair_small de h01 i j (mem_Ioc.mp hj).1)
  · calc Rde J de ≤ ∏ i ∈ Icc 1 J, ∏ j ∈ Ioc i J, Real.exp
            ((de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) := by
          unfold Rde
          have hnn : ∀ i j : ℕ, j ∈ Ioc i J → 0 ≤ 1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ))) := by
            intro i j hj
            have := abs_le.mp (pair_small de h01 i j (mem_Ioc.mp hj).1)
            linarith [this.1]
          refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j hj => hnn i j hj)
            fun i _ => ?_
          refine Finset.prod_le_prod (fun j hj => hnn i j hj) fun j hj => ?_
          rw [add_comm]; exact Real.add_one_le_exp _
      _ = Real.exp (∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) := by
          rw [Real.exp_sum]
          exact (Finset.prod_congr rfl fun i _ => Real.exp_sum _ _).symm
      _ ≤ Real.exp (((J : ℝ) + 1) / 4) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hlin.2]
end Formalism.FourierDecayAlt.P.Sz4
