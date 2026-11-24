-- Prove2me | solution 1 for Formalism.L2.Th1.H.TMv.lineRestr_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:48.378657+00:00
-- url     : https://prove2.me/submissions/298748ff-d1c6-4921-80e4-7b91e27de6f2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_TaylorMvLinear
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_IsogenyFormulaInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LineRestrLinSubst
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
theorem _root_.solution {K : Type*} [CommRing K] {n : Type*} [Fintype n] (a : Fin 4)
    (v : Fin 4 × n → K) (T : MvPowerSeries n K) :
    lineRestr v (MvPowerSeries.subst
      (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) T)
      = lineRestr (fun i => v (a, i)) T := by
  have hX : MvPowerSeries.HasSubst
      (fun i : n => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  unfold lineRestr
  rw [MvPowerSeries.subst_comp_subst_apply hX (hasSubst_line v)]
  congr 1
  funext i
  exact MvPowerSeries.subst_X (hasSubst_line v) (a, i)
end Formalism.L2.Th1.H.TMv
