-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.coeff_linR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:09.912826+00:00
-- url     : https://prove2.me/submissions/5e539396-6f50-4822-9e1e-8ac123136941

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
theorem _root_.solution (Ab B : Fin d → Fin d → S) (i0 l0 : Fin d) :
    coeff (sil i0 l0) (∑ i, ∑ l, C (B i l) * (xs S d (0 : Fin 2) i * PairEvaluation.lin Ab (1 : Fin 2) l)) =
      ∑ l, B i0 l * Ab l l0 := by
  have key : ∀ i l j, coeff (sil i0 l0) (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) :
      MvPolynomial (Fin 2 × Fin d) S) = if i = i0 ∧ j = l0 then B i l * Ab l j else 0 := by
    intro i l j
    rw [show (C (B i l) * (X ((0 : Fin 2), i) * (C (Ab l j) * X ((1 : Fin 2), j))) : MvPolynomial (Fin 2 × Fin d) S) =
      C (B i l * Ab l j) * (X ((0 : Fin 2), i) * X ((1 : Fin 2), j)) by rw [map_mul]; ring]
    rw [coeff_C_mul, coeff_XX]
    by_cases h : i = i0 ∧ j = l0
    · rw [if_pos (sil_inj.2 h), if_pos h, mul_one]
    · rw [if_neg (fun h' => h (sil_inj.1 h')), if_neg h, mul_zero]
  simp only [PairEvaluation.lin, xs, Finset.sum_mul, Finset.mul_sum, coeff_sum, key]
  rw [Finset.sum_eq_single i0 (fun i _ hi => Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun j _ => by simp [hi]) (by simp)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l0 (fun j _ hj => by simp [hj]) (by simp), if_pos ⟨rfl, rfl⟩]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
