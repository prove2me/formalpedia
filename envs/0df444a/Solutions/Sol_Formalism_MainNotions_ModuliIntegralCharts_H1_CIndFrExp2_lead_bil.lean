-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.lead_bil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:30:35.671071+00:00
-- url     : https://prove2.me/submissions/64d691f1-fc3d-4803-ae37-d3034da765c3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_bil_ext
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_eval_pair_bilinear
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_bilin_of_biadd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_const_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_lead_biadd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_stepNo2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_sub_homogeneousComponent_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ} (hm : 2 ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hu : IsUnit (coeff 0 P)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ 2 ∧
      P - 1 - bil (fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1))) ∈ Io S (Fin 2 × Fin d) ^ 3 ∧
      ∀ i l, coeff (sil i l) (homogeneousComponent 2 (P - 1)) = coeff (sil l i) (homogeneousComponent 2 (P - 1)) := by
  have h1 := const_one fF hF hph1 hu
  have h2 : P - 1 ∈ Io S _ ^ 2 := stepNo2 le_rfl (by omega) (by omega) fF hF hph1 hsym h1
  obtain ⟨hA1, hs⟩ := lead_biadd (j := 2) (by omega) hm fF hF hph1 hsym h2
  have hb := bilin_of_biadd hA1 hs
  set B := fun i l => coeff (sil i l) (homogeneousComponent 2 (P - 1)) with hB
  have hbB : homogeneousComponent 2 (P - 1) = bil B := hb
  refine ⟨h2, ?_, ?_⟩
  · rw [← hbB]; exact sub_homogeneousComponent_mem h2
  · have e1 : ev2 (bil B) (xs S d 1) (xs S d 0) = bil (fun i l => B l i) := by
      rw [eval_pair_bilinear, bil, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [xs]; ring
    rw [← hbB, hs, hbB] at e1
    intro i l
    have := congrFun (congrFun (bil_ext e1) i) l
    exact this
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
