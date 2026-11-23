-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.prod_cube2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:29.149649+00:00
-- url     : https://prove2.me/submissions/8f767060-fe16-4074-b448-5bfa414498ec

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 2 → (T ⟶ G)) :
    ∏ I : ULift (Finset (Fin 2)), h (psum G xs I.down) ^ cε 2 I =
      h 1 * (h (xs 0 * 1))⁻¹ * (h (xs 1 * 1))⁻¹ * h (xs 0 * (xs 1 * 1)) := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I : Finset (Fin 2) => h (psum G xs I) ^ cε 2 ⟨I⟩) (fun _ => rfl)).trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have c0 : cε 2 ⟨(∅ : Finset (Fin 2))⟩ = 1 := rfl
  have c1 : cε 2 ⟨({0} : Finset (Fin 2))⟩ = -1 := rfl
  have c2 : cε 2 ⟨({1} : Finset (Fin 2))⟩ = -1 := rfl
  have c3 : cε 2 ⟨({0, 1} : Finset (Fin 2))⟩ = 1 := rfl
  have p0 : psum G xs ∅ = 1 := rfl
  have p1 : psum G xs {0} = xs 0 * 1 := rfl
  have p2 : psum G xs {1} = xs 1 * 1 := rfl
  have p3 : psum G xs {0, 1} = xs 0 * (xs 1 * 1) := rfl
  rw [c0, c1, c2, c3, p0, p1, p2, p3]
  simp only [zpow_one, zpow_neg, _root_.mul_assoc]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
