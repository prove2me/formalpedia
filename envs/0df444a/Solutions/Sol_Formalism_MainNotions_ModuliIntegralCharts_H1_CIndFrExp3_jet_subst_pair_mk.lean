-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.jet_subst_pair_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:49.598356+00:00
-- url     : https://prove2.me/submissions/6d067ccc-881f-44d2-86ce-4f6e873effe3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_jetSubstP_mk
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
theorem _root_.solution {κ' : Type} (m : ℕ) (u v : Fin d → MvPolynomial κ' S) (P : MvPolynomial (Fin 2 × Fin d) S) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2)
        (Ideal.Quotient.mk (orig S (Fin 2 × Fin d) ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1))
        (ev2 P (fun j => u j - C (constantCoeff (u j))) (fun j => v j - C (constantCoeff (v j)))) := by
  have hf : (fun p : Fin 2 × Fin d => (![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2 -
      C (constantCoeff ((![u, v] : Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2))) =
      fun p : Fin 2 × Fin d => (![fun j => u j - C (constantCoeff (u j)), fun j => v j - C (constantCoeff (v j))] :
        Fin 2 → Fin d → MvPolynomial κ' S) p.1 p.2 := by
    funext p
    rcases p with ⟨k, j⟩
    fin_cases k <;> rfl
  rw [jetSubstP_mk, hf]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
