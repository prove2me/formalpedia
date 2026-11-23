-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:42.15614+00:00
-- url     : https://prove2.me/submissions/3e74bc57-fab3-451f-bc0a-afffa1487c0a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') (p : MvPolynomial ι R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
