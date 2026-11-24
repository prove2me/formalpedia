-- Prove2me | solution 1 for Formalism.L2.Th1.H.TMv.lineRestr_linSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:50.209838+00:00
-- url     : https://prove2.me/submissions/aebc57be-d2fe-46b5-977b-927f7668f51d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_mul
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_sum
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_C
import Theorems.Thm_Formalism_L2_Th1_H_TMv_lineRestr_X
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_congr
import Theorems.Thm_Formalism_L2_Th1_F_taylorDeriv
import Theorems.Thm_Formalism_L2_Th1_F_taylorRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.TMv
open Formalism.L2.Th1.F (taylor0 taylorRing taylorDeriv)
namespace Formalism.L2.Th1.H.TMv
theorem _root_.solution {K : Type*} [CommRing K] {m n : Type*} [Finite m] [Fintype n]
    (M : Matrix m n K) (v : n → K) (T : MvPowerSeries m K) :
    lineRestr v (linSubst M T) = lineRestr (M.mulVec v) T := by
  have hM : MvPowerSeries.HasSubst
      (fun i => ∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
  unfold linSubst
  conv_lhs => unfold lineRestr
  rw [MvPowerSeries.subst_comp_subst_apply hM (hasSubst_line v)]
  unfold lineRestr
  congr 1
  funext i
  change lineRestr v (∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K)) = _
  rw [lineRestr_sum]
  simp only [lineRestr_mul, lineRestr_C, lineRestr_X, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]
end Formalism.L2.Th1.H.TMv
