-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1.phOneVal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:25:34.563614+00:00
-- url     : https://prove2.me/submissions/77862ee9-9b28-4cf4-a37a-f3f3f897f2f7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SubstCoeRename
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh1_subst_coe_rename
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJPh1_val_pe_pair
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_psJet_subst_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_jpt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_gm_homAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGB_cc_psTrunc__670d9e4bd30f
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_val_scale__ccfcdc1cfe51
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const__a_6a1787d574a4
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_law__a_b638aaa98346
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
theorem _root_.solution : ExpGJ.PhOneValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ hx m u0 u1 u2 z J hJ
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hφ.const
  set us : Fin 3 → 𝓞 E := ![u0, u1, u2] with hus
  set P3 : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := fun k => φa c φ (us k) with hP3
  have hP3c : ∀ i j, MvPowerSeries.constantCoeff (P3 i j) = 0 := fun i j => const_φa c φ hφ0 (us i) j
  have hP3e : (![φa c φ u0, φa c φ u1, φa c φ u2] : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) = P3 := by
    refine funext fun k => ?_
    fin_cases k <;> rfl
  refine (C.frame.ph1 m).elim fun u huc => ?_
  have hu := huc.1
  have hcorr := huc.2
  refine ⟨Units.map (jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)).toMonoidHom u, ?_, ?_⟩
  · show jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (u : Jet S (Fin 3 × Fin C.d) m) = _
    rw [hu, jetSubstPS_psJet m (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (fun p => hP3c p.1 p.2), hP3e]
    rfl
  · have hv := val_corr hJ hcorr (ptm C P3 m).left

    have hmor : ptm C P3 m ≫ lift (jpt y C.d C.x m (0 : Fin 3)) (lift (jpt y C.d C.x m (1 : Fin 3)) (jpt y C.d C.x m (2 : Fin 3))) =
        xExp y C φ m ≫ lift (Xo.univ.t.act.act u0) (lift (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2)) := by
      rw [comp_lift, comp_lift, comp_lift, comp_lift, ptm_jpt C φ hφ0 hx m us 0, ptm_jpt C φ hφ0 hx m us 1,
        ptm_jpt C φ hφ0 hx m us 2]
      rfl
    have hL : val (ExpGC.cubAt (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2))
        (xExp y C φ m).left z J =
        val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
          (lift (jpt y C.d C.x m (0 : Fin 3)) (lift (jpt y C.d C.x m (1 : Fin 3)) (jpt y C.d C.x m (2 : Fin 3)))).left)
          (ptm C P3 m).left z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [← Over.comp_left, ← Over.comp_left, hmor]
    rw [hL, hv]

    rw [ExpGD.val_scale' _ _ _ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_inv]
    have hg : gm (ptm C P3 m).left z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤
        (unitΓ (Units.map (jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)).toMonoidHom u)) :=
      gm_homAt _ z u
    rw [hg]
    have hX : ∀ (b : Fin 3) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin C.d) S) : MvPowerSeries (Fin 3 × Fin C.d) S) = P3 b j := by
      intro b j
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (fun p : Fin 3 × Fin C.d => hP3c p.1 p.2))]
    have hF : ∀ j : Fin C.d, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m (φa c φ (u0 + u1) j) := by
      intro j
      unfold psIn
      rw [subst_coe_rename (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (fun p => hP3c p.1 p.2)]
      beta_reduce
      rw [psJet_subst_trunc m (fun t : Fin 2 × Fin C.d => P3 ((![0, 1] : Fin 2 → Fin 3) t.1) t.2)
        (fun t => hP3c _ t.2), ← law_φa c hφ u0 u1 j]
      congr 2
      funext p
      obtain ⟨b, i⟩ := p
      fin_cases b <;> rfl
    have hcX : ∀ (b : Fin 3) (j : Fin C.d), MvPolynomial.constantCoeff (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin C.d) S) = 0 :=
      fun b j => by simp
    have hcF : ∀ j : Fin C.d, MvPolynomial.constantCoeff (psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j)) = 0 := by
      intro j
      unfold psIn
      rw [MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', C.B.G.const]
    have hsA : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((((![fun j => psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) i j : MvPolynomial _ S)) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m ((![φa c φ (u0 + u1), φa c φ u2] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) := by
      intro i j
      fin_cases i
      · simpa using hF j
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((2 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u2 j)
        rw [hX]
        rfl
    have hsB : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((((![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) i j : MvPolynomial _ S)) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m ((![φa c φ u0, φa c φ u2] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) := by
      intro i j
      fin_cases i
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((0 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u0 j)
        rw [hX]
        rfl
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((2 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u2 j)
        rw [hX]
        rfl
    have hsC : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((((![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) i j : MvPolynomial _ S)) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m ((![φa c φ u1, φa c φ u2] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) := by
      intro i j
      fin_cases i
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((1 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u1 j)
        rw [hX]
        rfl
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((2 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u2 j)
        rw [hX]
        rfl
    have hQc : ∀ (a b : 𝓞 E) (i : Fin 2) (j : Fin C.d), MvPowerSeries.constantCoeff
        ((![φa c φ a, φa c φ b] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
      intro a b i j
      fin_cases i
      · exact const_φa c φ hφ0 a j
      · exact const_φa c φ hφ0 b j
    rw [val_pe_pair C m P3 hP3c _ (fun i j => by fin_cases i; exacts [hcF j, hcX 2 j]) _ (hQc _ _) hsA hJ,
      val_pe_pair C m P3 hP3c _ (fun i j => by fin_cases i; exacts [hcX 0 j, hcX 2 j]) _ (hQc _ _) hsB hJ,
      val_pe_pair C m P3 hP3c _ (fun i j => by fin_cases i; exacts [hcX 1 j, hcX 2 j]) _ (hQc _ _) hsC hJ,
      _root_.mul_assoc]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
