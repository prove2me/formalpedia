-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.low_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:00.945135+00:00
-- url     : https://prove2.me/submissions/05bcdeb8-2963-4e0f-bebc-499efbe2cf1d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_subst__b3c6c3b879e6
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_low_logOf
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
theorem _root_.solution (G : FGLaw S d) (b : Fin 2) (i : Fin d) :
    Low 2 (CIndFrFix.lg G b i - X (b, i)) := by
  have hk : ∀ p : Fin 1 × Fin d, Low 1 (![pt S d b] p.1 p.2) := by
    intro p
    rw [low_one_iff]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  have hk0 : ∀ p : Fin 1 × Fin d, constantCoeff (![pt S d b] p.1 p.2) = 0 :=
    fun p => (low_one_iff _).1 (hk p)
  have ha : HasSubst (fun p : Fin 1 × Fin d => ![pt S d b] p.1 p.2) := ⟨fun s => by rw [hk0 s]; exact IsNilpotent.zero, fun _ => Set.toFinite _⟩
  have e1 : CIndFrFix.lg G b i - X (b, i) =
      subst (fun p : Fin 1 × Fin d => ![pt S d b] p.1 p.2)
        (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i - X ((0 : Fin 1), i)) := by
    rw [← coe_substAlgHom ha, map_sub, coe_substAlgHom, subst_X ha]
    rfl
  rw [e1]
  exact low_subst' hk (low_logOf G i)
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
