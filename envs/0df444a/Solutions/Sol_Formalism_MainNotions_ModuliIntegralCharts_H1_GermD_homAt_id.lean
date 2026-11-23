-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:21.906533+00:00
-- url     : https://prove2.me/submissions/27d94387-46e5-4273-b5fe-bfe85279a606

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
theorem _root_.solution {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [homAt, spMap]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
