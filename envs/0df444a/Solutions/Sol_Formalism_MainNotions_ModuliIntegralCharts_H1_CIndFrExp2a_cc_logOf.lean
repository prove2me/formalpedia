-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.cc_logOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:44.624402+00:00
-- url     : https://prove2.me/submissions/9a2dc681-b43d-442b-95e9-eafa7706443d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne

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
theorem _root_.solution (G : FGLaw S d) (i : Fin d) : constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  show algebraMap ℚ S (((0 : Fin 1 × Fin d →₀ ℕ).degree : ℚ)⁻¹) * _ = 0
  simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
