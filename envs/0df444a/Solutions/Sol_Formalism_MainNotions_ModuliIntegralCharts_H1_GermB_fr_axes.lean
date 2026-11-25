-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.fr_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:33.854135+00:00
-- url     : https://prove2.me/submissions/8c64bdfa-d4b0-4512-904b-207a69a87d60

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_prod_cube2
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_first_axis_at_first_copy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_first_axis_at_second_copy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_second_axis_at_first_copy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_second_axis_at_second_copy
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_cgen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] [IsLocalRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
variable {t x0 d x}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) (i0 : t.PP.L.ι) (hi0 : (e0 t x0) ⁻¹ᵁ t.PP.L.U i0 = ⊤) :
    FrAxes t x0 d x (fr hch i0 hi0) := by
  have hL := t.PP.isLB
  have key : ∀ (m : ℕ) (σ : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m) (a b : jOG x0 d m 1 ⟶ t.G),
      homAt x0 σ ≫ jptG t x0 d x m (0 : Fin 2) = a → homAt x0 σ ≫ jptG t x0 d x m (1 : Fin 2) = b → (a = 1 ∨ b = 1) →
      LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)])
        (cε 2) (fr hch i0 hi0 m) (homAt x0 σ).left) (LB.oneGen t.PP.L) := by
    intro m σ a b ha hb hab
    refine corr_of_val hL fun y J hJ => ?_
    refine (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    have hI : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (homAt x0 σ).left) ≫
        cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I = (psum t.G ![a, b] I.down).left := by
      intro I
      rw [Category.id_comp]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
      fin_cases i
      · exact ha
      · exact hb
    rw [Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hI I)]
    have hc := prod_cube2 t.G (fun p : jOG x0 d m 1 ⟶ t.G => cv t.PP.L i0 y J p.left) ![a, b]
    rw [hc]
    rcases hab with rfl | rfl <;> simp
  intro m
  refine ⟨key m (axis0 d m) 1 (x m) ?_ ?_ (Or.inl rfl), key m (axis1 d m) (x m) 1 ?_ ?_ (Or.inr rfl)⟩
  · rw [jptG, ← Category.assoc, homAt_comp, first_axis_at_first_copy, ← homAt_comp, Category.assoc, hch.zero m]
    exact map_one (preHom (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) m))))
  · rw [jptG, ← Category.assoc, homAt_comp, first_axis_at_second_copy, homAt_id, Category.id_comp]
  · rw [jptG, ← Category.assoc, homAt_comp, second_axis_at_first_copy, homAt_id, Category.id_comp]
  · rw [jptG, ← Category.assoc, homAt_comp, second_axis_at_second_copy, ← homAt_comp, Category.assoc, hch.zero m]
    exact map_one (preHom (homAt x0 (Algebra.ofId S (Jet S (Fin 1 × Fin d) m))))
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
