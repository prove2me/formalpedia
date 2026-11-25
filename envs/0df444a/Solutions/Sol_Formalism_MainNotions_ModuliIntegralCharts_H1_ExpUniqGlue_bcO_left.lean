-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.bcO_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:03:42.304168+00:00
-- url     : https://prove2.me/submissions/426fa98e-d701-4a27-8a9f-9b8f94eeae9a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
variable {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
variable {X : Scheme.{0}} (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp S ⟶ X)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] (bA : A →+* A')
    (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f) :
    (bcO f x0 bA hA).left = Spec.map (CommRingCat.ofHom bA) := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
