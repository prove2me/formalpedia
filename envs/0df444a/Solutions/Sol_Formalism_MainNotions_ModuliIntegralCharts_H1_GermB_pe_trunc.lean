-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.pe_trunc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:46.253912+00:00
-- url     : https://prove2.me/submissions/d6b855af-6776-4a2e-9f71-e7d2564803ba

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetSubstP_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermB_jetSubstP_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {e : ∀ m, FrTyG t x0 d x m} (htr : FrTrunc t x0 d x e) {n : ℕ}
    (φ : ℕ → Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (hφ : ∀ m i j, φ (m + 1) i j - φ m i j ∈ orig S (Fin n × Fin d) ^ (m + 1))
    (m : ℕ) (y : (jOG x0 d m n).left) (J : ((jOG x0 d m n).left ⟶ t.G.left) → t.PP.L.ι) (hJ : Good t.PP.L y J) :
    val (peG t x0 d x e (m + 1) (φ (m + 1))) (ρn x0 d n m).left y J = val (peG t x0 d x e m (φ m)) (𝟙 _) y J := by
  have hc : (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2 :
      Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) = jetSubstP m fun p => φ m p.1 p.2 :=
    jetSubstP_congr m _ _ (fun p => hφ m p.1 p.2)
  have hcomp : (ρn x0 d n m).left ≫
      (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left =
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left ≫
        (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left := by
    rw [← Over.comp_left, ← Over.comp_left, homAt_comp, homAt_comp, jetSubstP_trunc]
  unfold peG
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetSubstP (m + 1) fun p : Fin 2 × Fin d => φ (m + 1) p.1 p.2)).left (ρn x0 d n m).left (z := y) (J := J)
  have h2 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e m)
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (𝟙 _) (z := y) (J := J)
  have h3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ (e (m + 1))
    (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left
    (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left (z := y) (J := J)
  have h4 : val (LB.pullGen t.PP.L _ _ (e (m + 1))
      (homAt x0 (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin d) m)).left)
      (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J =
      val (e m) (homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ m p.1 p.2)).left y J := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ (htr m) _
    | exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr (htr m) _ hJ
  try unfold peG
  refine h1.trans ?_
  rw [hcomp, hc]
  refine h3.symm.trans (h4.trans ?_)
  refine (h2.trans ?_).symm
  rw [Category.id_comp]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
