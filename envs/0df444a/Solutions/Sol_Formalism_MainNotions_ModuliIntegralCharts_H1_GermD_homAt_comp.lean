-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:58.357861+00:00
-- url     : https://prove2.me/submissions/f6db7aa1-686c-4907-938a-b47f0e261e04

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
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap, ← Spec.map_comp]
  rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
