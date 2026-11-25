-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ.adVal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:41:53.787612+00:00
-- url     : https://prove2.me/submissions/6d1c2007-a7a2-4801-9182-50272a572094

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhOneValSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpGJAd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJ_cc_psIn
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGJ_psJet_subst_psIn
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_const_substPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGF_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_jpt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGH_ptm_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGI_gm_homAt
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGD_val_scale__ccfcdc1cfe51
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_act__a_200fb8f04dea
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGG_const__a_6a1787d574a4
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 800000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
theorem _root_.solution : AdValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ hx hact a' wL hrel m u0 u1 z J hJ
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hφ.const
  obtain ⟨u, hu, hc⟩ := hrel m
  let P : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := ![φa c φ u0, φa c φ u1]
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 u0 j, fun j => const_φa c φ hφ0 u1 j⟩
  let Q : Fin 2 × Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := fun p => P p.1 p.2
  have hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0 := fun p => hP p.1 p.2
  have hQs : MvPowerSeries.HasSubst Q := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ
  have hQ0 : ∀ j, Q ((0 : Fin 2), j) = φa c φ u0 j := fun j => rfl
  have hQ1 : ∀ j, Q ((1 : Fin 2), j) = φa c φ u1 j := fun j => rfl

  have hpt : (ptm C P m).left ≫ (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left =
      (xExp y C φ m).left ≫ (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left := by
    have hPe : (fun k => φa c φ ((![u0, u1] : Fin 2 → 𝓞 E) k)) = P := by
      funext k
      refine Fin.cases rfl (fun k' => ?_) k
      rw [Fin.fin_one_eq_zero k']
      rfl
    have e0 := ptm_jpt C φ hφ0 hx m ![u0, u1] 0
    have e1 := ptm_jpt C φ hφ0 hx m ![u0, u1] 1
    rw [hPe] at e0 e1
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, e0, e1]
    rfl

  let σa : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S := fun p =>
    (![fun j => psIn C.d m ![0] (C.B.A.act a' j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
      Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2
  let σb : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S := fun p =>
    (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a') j)] :
      Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2
  have ea0 : ∀ j, σa ((0 : Fin 2), j) = psIn C.d m ![0] (C.B.A.act a' j) := fun j => rfl
  have ea1 : ∀ j, σa ((1 : Fin 2), j) = MvPolynomial.X ((1 : Fin 2), j) := fun j => rfl
  have eb0 : ∀ j, σb ((0 : Fin 2), j) = MvPolynomial.X ((0 : Fin 2), j) := fun j => rfl
  have eb1 : ∀ j, σb ((1 : Fin 2), j) = psIn C.d m ![1] (C.B.A.act (H.bar a') j) := fun j => rfl
  have hσa : ∀ k, MvPolynomial.constantCoeff (σa k) = 0 := by
    rintro ⟨i, j⟩
    revert j
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun j => by rw [ea0]; exact cc_psIn m 0 _ (C.B.A.const a' j), fun j => by rw [ea1]; simp⟩
  have hσb : ∀ k, MvPolynomial.constantCoeff (σb k) = 0 := by
    rintro ⟨i, j⟩
    revert j
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun j => by rw [eb0]; simp, fun j => by rw [eb1]; exact cc_psIn m 1 _ (C.B.A.const (H.bar a') j)⟩
  have hcc : ∀ (σ : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S), (∀ k, MvPolynomial.constantCoeff (σ k) = 0) →
      ∀ i j, MvPowerSeries.constantCoeff (MvPowerSeries.subst Q ((σ (i, j) : MvPolynomial _ S) :
        MvPowerSeries (Fin 2 × Fin C.d) S)) = 0 := by
    intro σ hσ i j
    refine const_substPS Q hQ _ ?_
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact hσ (i, j)
  have hPa : ∀ i j, MvPowerSeries.constantCoeff
      ((![φa c φ (a' * u0), φa c φ u1] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 _ j, fun j => const_φa c φ hφ0 _ j⟩
  have hPb : ∀ i j, MvPowerSeries.constantCoeff
      ((![φa c φ u0, φa c φ (H.bar a' * u1)] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 _ j, fun j => const_φa c φ hφ0 _ j⟩
  have hma : (ptm C P m).left ≫ (homAt y.x (jetSubstP m σa)).left = (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left := by
    rw [← Over.comp_left, ptm_subst C P hP m σa hσa]
    refine congrArg Over.Hom.left (ptm_congr C (hcc σa hσa) hPa m ?_)
    rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [ea0, psJet_subst_psIn m 0 Q hQ]
      exact congrArg (psJet m) (act_φa c hφ0 hact a' u0 j)
    · rw [ea1, MvPolynomial.coe_X, MvPowerSeries.subst_X hQs, hQ1]
      rfl
  have hmb : (ptm C P m).left ≫ (homAt y.x (jetSubstP m σb)).left =
      (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left := by
    rw [← Over.comp_left, ptm_subst C P hP m σb hσb]
    refine congrArg Over.Hom.left (ptm_congr C (hcc σb hσb) hPb m ?_)
    rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [eb0, MvPolynomial.coe_X, MvPowerSeries.subst_X hQs, hQ0]
      rfl
    · rw [eb1, psJet_subst_psIn m 1 Q hQ]
      exact congrArg (psJet m) (act_φa c hφ0 hact (H.bar a') u1 j)
  have va : val (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a' j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (ptm C P m).left z J = val (C.e m) (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left z J :=
    (show _ = val (C.e m) ((ptm C P m).left ≫ (homAt y.x (jetSubstP m σa)).left) z J from val_pull hJ _ _ _).trans
      (congrArg (fun r => val (C.e m) r z J) hma)
  have vb : val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a') j)])
      (ptm C P m).left z J = val (C.e m) (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left z J :=
    (show _ = val (C.e m) ((ptm C P m).left ≫ (homAt y.x (jetSubstP m σb)).left) z J from val_pull hJ _ _ _).trans
      (congrArg (fun r => val (C.e m) r z J) hmb)
  have vw : val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
      (ptm C P m).left z J =
      val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left)
        (xExp y C φ m).left z J := by
    rw [val_pull hJ, val_pull hJ, hpt]
  have hg : gm (ptm C P m).left z ⊤ (unitΓ u) =
      gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstPS (m := m) Q).toMonoidHom u)) :=
    ExpGI.gm_homAt _ z u
  have h1 := val_corr hJ hc (ptm C P m).left
  rw [val_mul hJ, ExpGD.val_scale' _ _ _ _ _ z J hJ, va, vb, vw, hg] at h1
  refine ⟨Units.map (jetSubstPS (m := m) Q).toMonoidHom u, ?_, ?_⟩
  · show jetSubstPS (m := m) Q (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (atP P (C.B.ad a'))
    rw [hu, jetSubstPS_psJet m Q hQ]
    rfl
  · rw [← _root_.mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h1
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
