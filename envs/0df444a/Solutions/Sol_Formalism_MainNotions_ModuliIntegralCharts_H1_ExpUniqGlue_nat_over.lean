-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.nat_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:51.264563+00:00
-- url     : https://prove2.me/submissions/cfc8e445-c780-41c7-8322-8e363812b0c0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_bcO_left

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
theorem _root_.solution {A A' B B' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra T A'] [CommRing B]
    [Algebra S B] [CommRing B'] [Algebra T B'] (bA : A →+* A') (hA : bA.comp (algebraMap S A) = (algebraMap T A').comp f)
    (bB : B →+* B') (hB : bB.comp (algebraMap S B) = (algebraMap T B').comp f)
    (ψ : A →ₐ[S] B) (ψ' : A' →ₐ[T] B') (e : (ψ' : A' →+* B').comp bA = bB.comp (ψ : A →+* B)) :
    homAt (x0T f x0) ψ' ≫ bcO f x0 bA hA = bcO f x0 bB hB ≫ homAt x0 ψ := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, bcO_left, homAt, Over.homMk_left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
