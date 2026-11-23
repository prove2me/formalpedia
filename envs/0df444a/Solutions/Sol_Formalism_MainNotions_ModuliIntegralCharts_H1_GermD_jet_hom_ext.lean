-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:15.345186+00:00
-- url     : https://prove2.me/submissions/4b43eac4-7a3b-4efe-ae84-ff91e77cb6c0

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
theorem _root_.solution {B : Type} [CommRing B] [Algebra R B] {f g : Jet R ι m →ₐ[R] B}
    (h : ∀ i, f (Ideal.Quotient.mk _ (X i)) = g (Ideal.Quotient.mk _ (X i))) : f = g :=
  Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun i => h i)
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
