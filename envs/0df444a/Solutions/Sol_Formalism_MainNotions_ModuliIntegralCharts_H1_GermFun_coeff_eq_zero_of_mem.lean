-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:59.819286+00:00
-- url     : https://prove2.me/submissions/2b715745-cdc9-462d-9658-7e37f8956af9

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_mem_ordGE
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_orig_pow_le

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
theorem _root_.solution {R ι : Type} [CommRing R] {n : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ orig R ι ^ n) {e : ι →₀ ℕ} (he : e.degree < n) : MvPolynomial.coeff e p = 0 := by
  by_contra hne
  have h1 := (mem_ordGE.1 (orig_pow_le R ι n hp)) e (MvPolynomial.mem_support_iff.2 hne)
  omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
