-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.mem_orig_of_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:05.726903+00:00
-- url     : https://prove2.me/submissions/9a1fd859-b5e6-4c5a-9763-36f67d84e183

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
theorem _root_.solution {κ : Type} (P : MvPolynomial κ S) (h : constantCoeff P = 0) : P ∈ orig S κ := by
  have hr : (Set.range (X : κ → MvPolynomial κ S)) = X '' Set.univ := Set.image_univ.symm
  show P ∈ Ideal.span (Set.range X)
  rw [hr, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm h
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hm0 (Finsupp.ext fun a => by simp [hcon a])
  exact ⟨i, Set.mem_univ _, hi⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
