-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.exists_ratioU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:28.130953+00:00
-- url     : https://prove2.me/submissions/4b3850a6-c9eb-42d7-bf5a-07a9d6cbf650

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_c__tr_5c2d9f8c1cdb
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_exists_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m) (he : ∀ m, (e m).IsGen)
    (m : ℕ) : ∃ U : (Jet S (Fin 2 × Fin d) m)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG x0 d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val (e (m + 1)) (r ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) z J =
        gm r z ⊤ (unitΓ U) * val (e m) r z J := by
  have hL := t.PP.isLB
  obtain ⟨u, hu⟩ := exists_ratio t.PP.L hL
    (φ := fun k => (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left ≫
      cφG t ![jptG t x0 d x (m + 1) (0 : Fin 2), jptG t x0 d x (m + 1) (1 : Fin 2)] k) (ε := cε 2)
    (fun U _ h => Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (cφ_tr hch m I))
    (LB.pullGen t.PP.L _ _ (e (m + 1)) _) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ (he (m + 1)) _) (e m) (he m)
  have hU : unitΓ (Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m))).hom.hom.toMonoidHom u) = u :=
    Units.ext (congrArg (fun f => CommRingCat.Hom.hom f u.val)
      (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m)))))
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (Jet S (Fin 2 × Fin d) m))).hom.hom.toMonoidHom u,
    fun Z r z J hJ => ?_⟩
  rw [hU]
  exact (val_pull hJ _ _ _).symm.trans (hu Z r z J hJ)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
