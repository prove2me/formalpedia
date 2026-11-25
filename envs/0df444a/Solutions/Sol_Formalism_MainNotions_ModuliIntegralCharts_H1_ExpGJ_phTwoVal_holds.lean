-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ.phTwoVal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:04.443536+00:00
-- url     : https://prove2.me/submissions/157c6dc9-a1a2-467b-b884-c9c00789e4d1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhTwoValHolds
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh2_ptm_pair
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh2_ptm_sum
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_jpt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_gm_homAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_val_scale__ccfcdc1cfe51
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const__a_6a1787d574a4
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh2
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
theorem _root_.solution : PhTwoValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hexp hx m u0 u1 u2 z J hJ
  have hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hexp.const
  obtain ⟨u, hu, hc⟩ := C.frame.ph2 m
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P3 C φ u0 u1 u2 i j) = 0 := fun i j => const_φa c φ hφ _ j
  have hPe : (P3 C φ u0 u1 u2) = ![φa c φ u0, φa c φ u1, φa c φ u2] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨Units.map (jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)).toMonoidHom u,
    ?_, ?_⟩
  · show jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2) (u : Jet S (Fin 3 × Fin C.d) m) = _
    rw [hu, jetSubstPS_psJet m (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2) (fun p => hP p.1 p.2), ← hPe]
    rfl
  · have h1 := val_corr hJ (DVR.corr_pullGen hc (ptm C (P3 C φ u0 u1 u2) m).left) (𝟙 _)
    have h2 := (val_pull hJ _ _ _).symm.trans (h1.trans (val_pull hJ _ _ _))
    have h3 := (val_pull hJ _ _ _).symm.trans h2
    simp only [Category.id_comp] at h3
    have hmor : (ptm C (P3 C φ u0 u1 u2) m).left ≫
        (lift (jpt y C.d C.x m (1 : Fin 3)) (lift (jpt y C.d C.x m (2 : Fin 3)) (jpt y C.d C.x m (0 : Fin 3)))).left =
        (xExp y C φ m).left ≫
          (lift (Xo.univ.t.act.act u1) (lift (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0))).left := by
      rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, comp_lift, comp_lift,
        ptm_jpt C φ hφ hx m ![u0, u1, u2] 1, ptm_jpt C φ hφ hx m ![u0, u1, u2] 2,
        ptm_jpt C φ hφ hx m ![u0, u1, u2] 0]
      rfl
    rw [hmor, ExpGD.val_scale' _ _ _ _ _ z J hJ] at h3
    rw [show val (ExpGC.cubAt (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2) (Xo.univ.t.act.act u0))
        (xExp y C φ m).left z J = _ from val_pull hJ _ _ _, h3]
    have hg : gm (ptm C (P3 C φ u0 u1 u2) m).left z ⊤ (unitΓ u) =
        gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstPS (m := m)
          (fun p : Fin 3 × Fin C.d => P3 C φ u0 u1 u2 p.1 p.2)).toMonoidHom u)) := gm_homAt _ z u
    rw [hg, val_mul hJ, val_mul hJ, val_inv, val_inv]
    rw [show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 3), j),
          fun j => psIn C.d m ![1, 2] (C.B.G.F j)]) (ptm C (P3 C φ u0 u1 u2) m).left z J =
        val (C.e m) ((ptm C (P3 C φ u0 u1 u2) m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => psIn C.d m ![1, 2] (C.B.G.F j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2)).left) z J from val_pull hJ _ _ _,
      show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 3), j),
          fun j => MvPolynomial.X ((1 : Fin 3), j)]) (ptm C (P3 C φ u0 u1 u2) m).left z J =
        val (C.e m) ((ptm C (P3 C φ u0 u1 u2) m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((1 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2)).left) z J from val_pull hJ _ _ _,
      show val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 3), j),
          fun j => MvPolynomial.X ((2 : Fin 3), j)]) (ptm C (P3 C φ u0 u1 u2) m).left z J =
        val (C.e m) ((ptm C (P3 C φ u0 u1 u2) m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
          (![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2)).left) z J from val_pull hJ _ _ _]
    rw [← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ptm_sum C φ hexp m u0 u1 u2,
      ptm_pair C φ hφ m u0 u1 u2 0 1, ptm_pair C φ hφ m u0 u1 u2 0 2]
    rw [mul_assoc (val (C.e m) (ptm C ![φa c φ u0, φa c φ (u1 + u2)] m).left z J)]
    rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
