-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio.pe_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:47:55.389006+00:00
-- url     : https://prove2.me/submissions/ba227033-30c4-433a-acbf-396fce175c67

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdPh_jetSubstP_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetSubstP_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetSubstP_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
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
theorem _root_.solution (e : ∀ m, FrTyG t x0 d x m) {n : ℕ} (m : ℕ) (v' v : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hv : ∀ i j, v' i j - v i j ∈ orig S (Fin n × Fin d) ^ (m + 1)) (y : (jOG x0 d m n).left)
    (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) v') (ρn x0 d n m).left y J =
      val (e (m + 1)) ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left) y J := by
  have hs : (ρn x0 d n m).left ≫ (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => v' p.1 p.2)).left =
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => v p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, jetSubstP_trunc,
      jetSubstP_congr m (fun p : Fin 2 × Fin d => v' p.1 p.2) (fun p : Fin 2 × Fin d => v p.1 p.2)
        (fun p => hv p.1 p.2)]
  exact (val_pull hJ (e (m + 1)) _ _).trans (congrArg (fun r => val (e (m + 1)) r y J) hs)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FrRatio
