-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.const_comp1_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:42.195948+00:00
-- url     : https://prove2.me/submissions/f5f89d3f-e450-496d-84ee-5df299bd0de6

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_ev

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {d : ℕ}
variable [Algebra ℚ S] [Algebra ℚ S']
variable {O : Type} [CommRing O] [StarRing O]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
theorem _root_.solution (B : FB S d O) (a : O) (i : Fin d) :
    constantCoeff (comp1 (B.actK S a) (pt S (n := 1) d 0) i) = 0 := by
  have h1 : ∀ j l, constantCoeff ((![pt S (n := 1) d 0] : Fin 1 → Pt S 1 d) j l) = 0 := by
    intro j l
    fin_cases j
    simp [pt]
  simp only [comp1]
  rw [const_ev _ h1]
  simp [FB.actK, B.A.const]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
