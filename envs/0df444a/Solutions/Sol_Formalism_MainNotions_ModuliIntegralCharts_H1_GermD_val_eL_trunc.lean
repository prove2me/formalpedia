-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.val_eL_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:52.228266+00:00
-- url     : https://prove2.me/submissions/dcb089c5-948b-4efe-9453-3a2e923d878a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_sL_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) (e : ∀ m, FrTyG t x0 d x m) (wP : PrimTyG t)
    (htr : FrTrunc t x0 d x e) (m : ℕ) (y : (jOG x0 d m 1).left) (J : ((jOG x0 d m 1).left ⟶ t.G.left) → t.PP.L.ι)
    (hJ : Good t.PP.L y J) :
    val (eLG t x0 d x act e wP (m + 1)) (ρT x0 d m).left y J = val (eLG t x0 d x act e wP m) (𝟙 _) y J := by
  have hx : (ρT x0 d m).left ≫ (x (m + 1)).left = (x m).left := by
    rw [← Over.comp_left, hch.trunc m]
  have hs : (ρT x0 d m).left ≫ (homAt x0 (sL (m + 1) (act H.w0))).left =
      (homAt x0 (sL m (act H.w0))).left ≫ (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, sL_trunc]
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
  · exact (val_pull hJ wP _ _).trans ((congrArg (fun r => val wP r y J) (hx.trans (Category.id_comp _).symm)).trans
      (val_pull hJ wP _ _).symm)
  · exact (val_pull hJ (e (m + 1)) _ _).trans ((congrArg (fun r => val (e (m + 1)) r y J) hs).trans
      ((val_pull hJ (e (m + 1)) _ _).symm.trans ((val_corr hJ (htr m) _).trans
        ((congrArg (fun r => val (e m) r y J) (Category.id_comp _).symm).trans (val_pull hJ (e m) _ _).symm))))
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
