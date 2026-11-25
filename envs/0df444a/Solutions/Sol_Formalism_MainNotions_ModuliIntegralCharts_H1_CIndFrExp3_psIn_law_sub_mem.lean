-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3.psIn_law_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:49.540862+00:00
-- url     : https://prove2.me/submissions/38877e46-cee5-4a06-be48-347acbbf6cc1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BalOf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IsUnitCoeffZero
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2_psTrunc_law_sub_mem
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdPh_cc_psIn
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_aeval_mem_pow
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
variable [Algebra ℚ S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
theorem _root_.solution (G : FGLaw S d) {m : ℕ} (hm : 1 ≤ m) (i : Fin d) :
    psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i) - C (constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i))) - (xs S d 0 i + xs S d 1 i) ∈
      Io S (Fin 3 × Fin d) ^ 2 := by
  have hc : constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i)) = 0 := by rw [FBIdPh.cc_psIn]; exact G.const i
  have hr : (rename fun p : Fin 2 × Fin d => (((![0, 1] : Fin 2 → Fin 3) p.1), p.2) :
      MvPolynomial (Fin 2 × Fin d) S →ₐ[S] MvPolynomial (Fin 3 × Fin d) S) =
      aeval (fun p : Fin 2 × Fin d => (X (((![0, 1] : Fin 2 → Fin 3) p.1), p.2) : MvPolynomial (Fin 3 × Fin d) S)) := by
    ext p; simp
  have e : psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i) - C (constantCoeff (psIn d m (![0, 1] : Fin 2 → Fin 3) (G.F i))) - (xs S d 0 i + xs S d 1 i) =
      aeval (fun p : Fin 2 × Fin d => (X (((![0, 1] : Fin 2 → Fin 3) p.1), p.2) : MvPolynomial (Fin 3 × Fin d) S))
        (psTrunc m (G.F i) - (X ((0 : Fin 2), i) + X ((1 : Fin 2), i))) := by
    rw [hc, map_zero, sub_zero, psIn, hr, map_sub, map_add, aeval_X, aeval_X]
    rfl
  rw [e]
  exact aeval_mem_pow _ (fun p => Ideal.subset_span ⟨_, rfl⟩) 2 (psTrunc_law_sub_mem G hm i)
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp3
