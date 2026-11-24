-- Prove2me | solution 1 for Formalism.L2.Th1.H.TMv.lineRestr_at1_eq_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:47.674534+00:00
-- url     : https://prove2.me/submissions/09c629a9-9dca-41ab-81aa-cee622c124f0

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
theorem _root_.solution {K n : Type} [Field K] [Finite n] (v : n → K) (i : n) (f : PowerSeries K) :
    lineRestr v (Formalism.InvariantFactorPaths.G7.at1 i f) = PowerSeries.rescale (v i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  unfold Formalism.InvariantFactorPaths.G7.at1 lineRestr
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hX (hasSubst_line v),
    PowerSeries.rescale_eq_subst, PowerSeries.subst_def, PowerSeries.smul_eq_C_mul]
  congr 1
  funext _
  exact MvPowerSeries.subst_X (hasSubst_line v) i
end Formalism.L2.Th1.H.TMv
