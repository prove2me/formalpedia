-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.tie_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:36.111046+00:00
-- url     : https://prove2.me/submissions/619dd227-25f3-440d-8ffe-4d48e5435c26

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBCNab
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_psJet_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_exp_pow_inv
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_isValueAt_of_eq
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_homAt_j__jBase_2a7168f2da0a
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTiePf_appTop_to__408424b20004
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndBCNab_const_hL
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_const_subst0
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst0
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_corr_genPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_corr_pullGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_corr_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_genPow_scale_pull
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_isPullSec_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_isPullSec_congr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_isValueAt_pullScale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_one
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_exists_pullSec
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_gen_eq_of_corr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_nabVal_eq_const
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_tie_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
open MvPowerSeries ExpTieAlg ExpTieGerm ExpTiePf
attribute [local instance] Over.cartesianMonoidalCategory
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : TieSt := by
  intro E _ _ _ H Dw l Xo c _ _ S _ _ _ y C φ hφ e he k F f hf
  have hL := Xo.univ.t.PP.isLB
  have hs0 : HasSubst (famL φ) := hasSubst0 fun p => hφ.const p.2
  have hhL : constantCoeff (C.B.hL S C.h H.w0) = 0 := CIndBCNab.const_hL C.B C.h C.gauge H.w0
  refine ⟨compL φ (f * Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)), fun m => ?_, fun α => ?_⟩
  · obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
    obtain ⟨u, hu, hCe⟩ := he m
    obtain ⟨F₂, hP₂⟩ := GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (Formalism.L2.Pj.homAt y.x (jφ φ m) ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F₁
    let τ₂ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (xExp y C φ m).left) fun _ => (k : ℤ)) :=
      ⟨fun j => (e m).s j ^ k⟩
    have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ₂
        (scaleGen _ _ (unitΓ u ^ k) (LB.pullGen Xo.univ.t.PP.L _ _
          (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k) (Formalism.L2.Pj.homAt y.x (jφ φ m)).left)) := by
      have := corr_genPow hCe k
      rw [genPow_scale_pull] at this
      exact this
    have h1 : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (scaleGen _ _ (unitΓ u ^ k) (LB.pullGen Xo.univ.t.PP.L _ _ τ₁ (Formalism.L2.Pj.homAt y.x (jφ φ m)).left))
        (scaleGen _ _ (unitΓ u ^ k) (LB.pullGen Xo.univ.t.PP.L _ _
          (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k) (Formalism.L2.Pj.homAt y.x (jφ φ m)).left)) :=
      corr_scale (corr_pullGen _ hC₁ _) _
    have heq := GermFun.gen_eq_of_corr _ hL _ _ _ _ _ τ₂ _ h1 hG
    refine ⟨F₂, τ₂, isPullSec_congr _ _ _ (homAt_jφ_jBase y C φ m) (isPullSec_comp _ _ _ _ _ hP₁ hP₂), ?_, ?_⟩
    · intro j j' _ _ c3
      have : j = j' := funext fun i => c3 i i rfl
      subst this
      rfl
    · rw [← heq]
      have hval := isValueAt_pullScale hL (k : ℤ) (Formalism.L2.Pj.homAt y.x (jφ φ m)) hP₂ hV₁ (unitΓ u ^ k)
      have hb : constantCoeff (compL φ (C.B.hL S C.h H.w0)) = 0 := by
        unfold compL
        rw [const_subst0 (a := famL φ) (fun p => hφ.const p.2)]
        exact hhL
      have hsub : subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0)) =
          PowerSeries.subst ((k : S) • compL φ (C.B.hL S C.h H.w0)) (PowerSeries.exp S) := by
        unfold Germ.FB.expS
        rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp (famL φ) (fun p => hφ.const p.2)
          (by rw [smul_eq_C_mul, map_mul, hhL, mul_zero]), subst_smul hs0]
        rfl
      have hprod : psJet m (subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0))) * ↑(u ^ k) = 1 := by
        rw [Units.val_pow_eq_pow_val, hu, ← psJet_pow, ← FBIdJet.psJet_mul, hsub]
        unfold Germ.FB.expS
        rw [exp_pow_inv _ hb k]
        exact FBIdJet.psJet_one m
      have hinv : psJet m (subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0))) = ↑((u ^ k)⁻¹) := by
        set X := psJet m (subst (famL φ) (Germ.FB.expS S ((k : S) • C.B.hL S C.h H.w0))) with hX
        calc X = X * ((↑(u ^ k) : Jet S (Fin 1 × Fin (dL Dw)) m) * ↑((u ^ k)⁻¹)) := by
              rw [Units.mul_inv, _root_.mul_one]
          _ = (X * ↑(u ^ k)) * ↑((u ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
          _ = ↑((u ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
      have hu' : ((unitΓ u ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin (dL Dw)) m), ⊤)ˣ) = unitΓ ((u ^ k)⁻¹) := by
        simp [unitΓ, map_pow, map_inv]
      refine isValueAt_of_eq _ _ _ hval ?_
      rw [appTop_toΓ, hu']
      show toΓ (Jet S (Fin 1 × Fin (dL Dw)) m) _ * toΓ (Jet S (Fin 1 × Fin (dL Dw)) m) _ =
        toΓ (Jet S (Fin 1 × Fin (dL Dw)) m) _
      rw [← map_mul]
      congr 1
      symm
      unfold compL jφ
      rw [jetSubstPS_psJet φ hφ.const m f, subst_mul hs0, FBIdJet.psJet_mul]
      congr 1
  · rw [nabVal_eq_const, tie_alg C.B.G.F C.uvec φ hφ α]
end Formalism.MainNotions.ModuliIntegralCharts.H1
