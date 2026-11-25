-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.bal_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:52:52.427923+00:00
-- url     : https://prove2.me/submissions/2f333573-b126-46b2-a3ab-72276c6c9176

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
theorem _root_.solution {R : Type} [CommRing R] [Algebra S R] (cc M N : Matrix (Fin d) (Fin d) S)
    (hbal : Matrix.transpose M * cc = cc * N) (u v : Fin d → R) :
    ∑ i, ∑ l, cc i l • ((∑ k, M i k • u k) * v l) = ∑ i, ∑ l, cc i l • (u i * ∑ k, N l k • v k) := by
  have key : ∀ a b, ∑ i, cc i b * M i a = ∑ l, cc a l * N l b := by
    intro a b
    have h := congrFun (congrFun hbal a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hL : ∑ i, ∑ l, cc i l • ((∑ k, M i k • u k) * v l) =
      ∑ a, ∑ b, (∑ i, cc i b * M i a) • (u a * v b) := by
    simp only [Finset.sum_mul, Finset.smul_sum, Finset.sum_smul, smul_mul_assoc, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact Finset.sum_comm
  have hR : ∑ i, ∑ l, cc i l • (u i * ∑ k, N l k • v k) =
      ∑ a, ∑ b, (∑ l, cc a l * N l b) • (u a * v b) := by
    simp only [Finset.mul_sum, Finset.smul_sum, Finset.sum_smul, mul_smul_comm, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_comm
  rw [hL, hR]
  simp only [key]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
