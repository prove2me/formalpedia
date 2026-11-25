-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.ev_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:29.956421+00:00
-- url     : https://prove2.me/submissions/9b011654-cac4-450d-a033-8d341d1109e7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PartialDerivativeExponent_subst_mem


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
theorem _root_.solution {m : ℕ} (V : Set (Fin n × Fin d)) (a : Fin m → Pt R n d)
    (h0 : ∀ q i, constantCoeff (a q i) = 0) (hV : ∀ q i, a q i ∈ subV R V) (g : PS R m d) :
    ev a g ∈ subV R V := by
  have hs : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => h0 p.1 p.2
  exact subst_mem (fun p : Fin m × Fin d => a p.1 p.2) hs (fun p => hV p.1 p.2) g
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
