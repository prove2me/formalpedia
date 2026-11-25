-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr.unit_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:50.145614+00:00
-- url     : https://prove2.me/submissions/2e147d4a-d33e-499a-8e3c-480cd70d2cd4

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrC

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
theorem _root_.solution {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  obtain ⟨hpb, hmul⟩ := h
  let x₀ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G := Over.homMk (η[G'].left ≫ φ) (by
    show (η[G'].left ≫ φ) ≫ G.hom = (𝟙_ (Over S')).hom ≫ f
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w η[G']])
  have hη : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    show toUnit (𝟙_ (Over S')) ≫ η[G'] = η[G']
    first
    | rw [toUnit_unit, Category.id_comp]
    | rw [Subsingleton.elim (toUnit (𝟙_ (Over S'))) (𝟙 _), Category.id_comp]
  have h2 := hmul (𝟙_ (Over S')) η[G'] η[G'] x₀ x₀ rfl rfl
  have hidem : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, ← hη, _root_.one_mul]
    rfl
  have h1 : x₀ = 1 := by
    first
    | exact mul_eq_left.1 hidem
    | exact mul_right_eq_self.1 hidem
  have h3 : x₀.left = (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ η[G]).left :=
    congrArg (fun g => g.left) h1
  rw [Over.comp_left] at h3
  have h4 : (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f))).left = f := by
    first
    | simp
    | simpa using Over.w (toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)))
  rw [h4] at h3
  exact h3
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
