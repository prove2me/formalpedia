-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD.jet_zero_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:49.995809+00:00
-- url     : https://prove2.me/submissions/2df42a2b-5f11-440a-a7f9-9c6f8f1268d2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetPointZeroEqOne
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
theorem _root_.solution {S : Type} [CommRing S] {κ κ' : Type} (f g : Jet S κ 0 →ₐ[S] Jet S κ' 0) : f = g := by
  apply jet_hom_ext
  intro i
  have h0 : (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.X i) : Jet S κ 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one]; exact X_mem_orig i)
  rw [h0, map_zero, map_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGD
