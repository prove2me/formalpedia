-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab.map_DpolyOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:17.553809+00:00
-- url     : https://prove2.me/submissions/3bdd91f2-0948-482d-9498-4697c5551d24

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_map_DmonOf

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
theorem _root_.solution (F : Fin d → PS S 2 d) {κ : Type} [Fintype κ] (u : κ → Fin d → S)
    (P : MvPolynomial κ S) (f : PS S 1 d) :
    map ψ (DpolyOf F u P f) =
      DpolyOf (fun j => map ψ (F j)) (fun l i => ψ (u l i)) (MvPolynomial.map ψ P) (map ψ f) := by
  simp only [DpolyOf, map_sum, map_mul, MvPowerSeries.map_C, map_DmonOf, MvPolynomial.coeff_map]
  symm
  apply Finset.sum_subset (MvPolynomial.support_map_subset ψ P)
  intro e _ he
  have h0 : ψ (P.coeff e) = 0 := by
    simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map] using he
  simp [h0]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndBCNab
