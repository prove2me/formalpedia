-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.const_hL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:31.891512+00:00
-- url     : https://prove2.me/submissions/bfcc8639-5f4a-4130-a9cb-d4842fb4b830

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_ev
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_pair

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
theorem _root_.solution (B : FB S d O) (h : PS S 2 d) (hh : B.IsCanonGauge S h) (w0 : O) :
    constantCoeff (B.hL S h w0) = 0 := by
  simp only [FB.hL]
  rw [const_ev _ (const_pair B w0)]
  have h2 : ∀ j i, constantCoeff ((![0, pt S (n := 1) d 0] : Fin 2 → Pt S 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  have h3 := congrArg constantCoeff hh.ax0
  rwa [const_ev _ h2, map_zero] at h3
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
