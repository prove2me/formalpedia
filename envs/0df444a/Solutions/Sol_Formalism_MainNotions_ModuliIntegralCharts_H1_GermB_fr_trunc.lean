-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.fr_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:38.877845+00:00
-- url     : https://prove2.me/submissions/4930dbca-0a1b-472c-8729-be3d9e26629c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jpt_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_val_cgen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
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
    FrTrunc t x0 d x (fr hch i0 hi0) := fun m => corr_of_val t.PP.isLB fun y J hJ => by
  have hmor : ∀ I : ULift (Finset (Fin 2)),
      (𝟙 _ ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) ≫
        cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] I =
      𝟙 _ ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
    intro I
    rw [Category.id_comp, Category.id_comp, vec2 (fun i => jptG t x0 d x (m + 1) i),
      vec2 (fun i => jptG t x0 d x m i)]
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
  exact (val_pull hJ _ _ _).trans ((val_cgen _ _ _ _ _ _ y J hJ).trans
    (Eq.trans (Finset.prod_congr rfl fun I _ => congrArg (fun ψ => cv t.PP.L i0 y J ψ ^ cε 2 I) (hmor I))
      (val_cgen _ _ _ _ _ _ y J hJ).symm))
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
