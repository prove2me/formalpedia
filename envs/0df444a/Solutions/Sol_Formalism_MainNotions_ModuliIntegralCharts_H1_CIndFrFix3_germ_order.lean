-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.germ_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:32.671947+00:00
-- url     : https://prove2.me/submissions/c0d1913d-f5aa-4144-8d1a-4a3e9d0816c6

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_unit_jet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_genPow_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_mulGen_scale_right
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_isValueAt_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix3_corr_pull_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_corr_genPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_corr_refl
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_corr_scale
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdLB_unit__homAt_215ffcb691bb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_refl
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 1000000
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)] (y : FrPt Xo c S)
    (C : ChartAt Xo c y) (e' : ∀ m, FrTy y C.d C.x m) (cc : ℕ → Fin C.d → Fin C.d → S)
    (he : ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m)))
    (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) (f : MvPowerSeries (Fin 1 × Fin C.d) S)
    (hf : IsGerm y C.d C.x C.B.A.act C.e C.wP k F f) (m : ℕ) :
    ∃ (F' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (jO y C.d m 1)))
      (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (C.x m).left) fun _ => (k : ℤ))),
      IsPullSec Xo.univ.t.G Xo.univ.t.PP.L k (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F F' ∧
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k) ∧
      IsValueAt Xo.univ.t.G Xo.univ.t.PP.L k F' (C.x m) τ
        (toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 (cc m))))) := by
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨u, hu, hCe⟩ := he m
  have h1 := corr_pull_scale _ _ (e' m) (C.e m) (unitΓ u) (homAt y.x (GermD.sL m (C.B.A.act H.w0))).left hCe
  rw [FBIdLB.unitΓ_homAt] at h1
  have hEL : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (eL y C.d C.x C.B.A.act e' C.wP m)
      (scaleGen _ _ (unitΓ (Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u))
        (eL y C.d C.x C.B.A.act C.e C.wP m)) := by
    have h2 := ReciprocityTheory.ChartRestriction.G.DVR.corr_mulGen
      (ExpTieGerm.corr_refl (L := Xo.univ.t.PP.L) (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (C.x m).left)) h1
    rw [mulGen_scale_right] at h2
    exact h2
  set U : (Jet S (Fin 1 × Fin C.d) m)ˣ := Units.map (GermD.sL m (C.B.A.act H.w0)).toMonoidHom u with hU
  set w : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ := unitΓ U with hw
  have hG : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (genPow _ _ (eL y C.d C.x C.B.A.act e' C.wP m) k)
      (scaleGen _ _ (w ^ k) (genPow _ _ (eL y C.d C.x C.B.A.act C.e C.wP m) k)) := by
    have := ExpTieGerm.corr_genPow hEL k
    rwa [genPow_scale] at this
  have h3 := ExpTieGerm.corr_scale hC₁ (w ^ k)
  have hC' := ReciprocityTheory.ChartRestriction.G.DVR.corr_trans hL h3 (ReciprocityTheory.ChartRestriction.G.DVR.corr_symm hG)
  have hV' := isValueAt_scale hV₁ (w ^ k)
  have hprod := unit_jet C.B H.w0 (cc m) m k u hu
  have hinv : psJet m (expP ((k : S) • diagL C.B H.w0 (cc m))) = ↑((U ^ k)⁻¹) := by
    set X := psJet m (expP ((k : S) • diagL C.B H.w0 (cc m))) with hX
    calc X = X * ((↑(U ^ k) : Jet S (Fin 1 × Fin C.d) m) * ↑((U ^ k)⁻¹)) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = (X * ↑(U ^ k)) * ↑((U ^ k)⁻¹) := (_root_.mul_assoc _ _ _).symm
      _ = ↑((U ^ k)⁻¹) := by rw [hprod, _root_.one_mul]
  have hw' : ((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) = unitΓ ((U ^ k)⁻¹) := by
    simp [hw, unitΓ, map_pow, map_inv]
  refine ⟨F₁, _, hP₁, hC', ?_⟩
  have hv : toΓ _ (psJet m (f * expP ((k : S) • diagL C.B H.w0 (cc m)))) =
      toΓ _ (psJet m f) * (((w ^ k)⁻¹ : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)ˣ) : Γ(Sp (Jet S (Fin 1 × Fin C.d) m), ⊤)) := by
    rw [hw']
    show _ = toΓ _ _ * toΓ _ _
    rw [← map_mul, FBIdJet.psJet_mul, hinv]
  rw [hv]
  exact hV'
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
