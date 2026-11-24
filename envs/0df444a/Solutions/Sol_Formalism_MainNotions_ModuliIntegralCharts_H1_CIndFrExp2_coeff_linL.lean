-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.coeff_linL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:34.811163+00:00
-- url     : https://prove2.me/submissions/c5890066-e2cc-4878-a13d-8d24f01e2d77

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_sil_inj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_coeff_XX
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
theorem _root_.solution (A B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (PairEvaluation.lin A (0 : Fin 2) i * xs S d (1 : Fin 2) l)) =
      ∑ i, A i i0 * B i l0 := by
  have key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) :
      MvPolynomial (Fin 2 × Fin d) S) = if j = i0 ∧ l = l0 then B i l * A i j else 0 := by
    intro i l j
    rw [show (C (B i l) * (C (A i j) * X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) : MvPolynomial (Fin 2 × Fin d) S) =
      C (B i l * A i j) * (X ((0 : Fin 2), j) * X ((1 : Fin 2), l)) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_XX]
    by_cases h : j = i0 ∧ l = l0
    · rw [if_pos (sil_inj.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]
  simp only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single l0 (fun l _ hl => Finset.sum_eq_zero fun j _ => by simp [hl]) (by simp)]
  rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩, mul_comm]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
