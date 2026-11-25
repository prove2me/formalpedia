-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA.exists_eG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:40.126801+00:00
-- url     : https://prove2.me/submissions/342cbe5b-09f4-4fed-a2e2-6b61a55aa765

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGA_scaleGen_isGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGA_exists_tau
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGA_exists_uJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scaleGen_isGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res h1 x) = ReciprocityTheory.ChartRestriction.G.Semi.res (h2.trans h1) x := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, Units.coe_map, MonoidHom.coe_coe]
     rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ← Functor.map_comp_apply])
private lemma pullU_res_lemma_2 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.pullU f V (ReciprocityTheory.ChartRestriction.G.Semi.res h x) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (fun _ hy => h hy)) (ReciprocityTheory.ChartRestriction.G.Semi.pullU f U x) := by
  apply Units.ext
  first
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
       Scheme.Hom.naturality]; rfl)
  | (simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.coe_map, MonoidHom.coe_coe]
     exact (Scheme.Hom.naturality_apply f (homOfLE h).op _).symm)
  | (simp [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, ← Scheme.Hom.naturality_apply])
private lemma pullU_comp_lemma_3 {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.pullU (g ≫ f) U x = ReciprocityTheory.ChartRestriction.G.Semi.pullU g (f ⁻¹ᵁ U) (ReciprocityTheory.ChartRestriction.G.Semi.pullU f U x) := by
  first
  | rfl
  | (apply Units.ext; rfl)
  | (apply Units.ext; simp [ReciprocityTheory.ChartRestriction.G.Semi.pullU, Scheme.comp_app])
private lemma pullGen_isGen_lemma_4 {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {c : LB.Gen (LB.LinComb L φ ε)} (hc : c.IsGen) {h : Z ⟶ Y} :
    (LB.pullGen L φ ε c h).IsGen := by
  intro i j
  have Pi : ∀ i', LB.wchart L (fun k => h ≫ φ k) i' ≤ h ⁻¹ᵁ LB.wchart L φ i' :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have T : LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j) :=
    le_inf (inf_le_left.trans (Pi i)) (inf_le_right.trans (Pi j))
  have H0 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) inf_le_left) (@id (Γ(Y, LB.wchart L φ i)ˣ) (c.s i)) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) inf_le_right) (@id (Γ(Y, LB.wchart L φ j)ˣ) (c.s j)) := hc i j
  have H := congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res T (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ i ⊓ LB.wchart L φ j) z)) H0
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart L (fun k => h ≫ φ k) i) inf_le_left) (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi i) (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ i) (@id (Γ(Y, LB.wchart L φ i)ˣ) (c.s i)))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ (h ≫ φ k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (h ≫ φ k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) i ⊓ LB.wchart L (fun k => h ≫ φ k) j ≤ LB.wchart L (fun k => h ≫ φ k) j) inf_le_right) (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi j) (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j) (@id (Γ(Y, LB.wchart L φ j)ˣ) (c.s j))))
  simp only [map_mul, map_prod, map_zpow, res_res_lemma, pullU_res_lemma_2, pullU_comp_lemma_3] at H ⊢
  exact H
private lemma corr_pull_lemma_6 {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {a : LB.Gen (LB.LinComb L φ ε)}
    {b : LB.Gen (LB.LinComb L φ' ε')} (hab : LB.Gen.Corr L φ ε φ' ε' a b) {h : Z ⟶ Y} :
    LB.Gen.Corr L (fun k => h ≫ φ k) ε (fun k => h ≫ φ' k) ε' (LB.pullGen L φ ε a h) (LB.pullGen L φ' ε' b h) := by
  intro j j' hj hj' hjj'
  have H1 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ j) inf_le_left) (@id (Γ(Y, LB.wchart L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ j ⊓ LB.wchart L φ' j' ≤ LB.wchart L φ' j') inf_le_right) (@id (Γ(Y, LB.wchart L φ' j')ˣ) (b.s j')) :=
    hab j j' (fun k₁ k₂ e => hj k₁ k₂ (by simp only [e])) (fun k₁ k₂ e => hj' k₁ k₂ (by simp only [e]))
      (fun k k' e => hjj' k k' (by simp only [e]))
  have Pa : LB.wchart L (fun k => h ≫ φ k) j ≤ h ⁻¹ᵁ LB.wchart L φ j := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have Pb : LB.wchart L (fun k => h ≫ φ' k) j' ≤ h ⁻¹ᵁ LB.wchart L φ' j' := fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have T : LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ h ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ' j') := le_inf (inf_le_left.trans Pa) (inf_le_right.trans Pb)
  have H := congrArg (fun z => ReciprocityTheory.ChartRestriction.G.Semi.res T (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j ⊓ LB.wchart L φ' j') z)) H1
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ LB.wchart L (fun k => h ≫ φ k) j) inf_le_left) (ReciprocityTheory.ChartRestriction.G.Semi.res Pa (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ j) (@id (Γ(Y, LB.wchart L φ j)ˣ) (a.s j)))) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (fun k => h ≫ φ k) j ⊓ LB.wchart L (fun k => h ≫ φ' k) j' ≤ LB.wchart L (fun k => h ≫ φ' k) j') inf_le_right) (ReciprocityTheory.ChartRestriction.G.Semi.res Pb (ReciprocityTheory.ChartRestriction.G.Semi.pullU h (LB.wchart L φ' j') (@id (Γ(Y, LB.wchart L φ' j')ˣ) (b.s j'))))
  simp only [res_res_lemma, pullU_res_lemma_2] at H ⊢
  exact H
private lemma corr_scale_lemma_7 {Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ Xo.univ.t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ Xo.univ.t.G.left)} {ε' : K' → ℤ}
    {v : Γ(Y, ⊤)ˣ} {a : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} {b : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ' ε')}
    (hab : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' a b) :
    LB.Gen.Corr Xo.univ.t.PP.L φ ε φ' ε' (scaleGen φ ε v a) (scaleGen φ' ε' v b) := by
  intro j j' hj hj' hjj'
  have H0 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ j) inf_le_left) (@id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ' j') inf_le_right) (@id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ' j')ˣ) (b.s j')) := hab j j' hj hj' hjj'
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ j) inf_le_left)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ≤ ⊤) le_top) v * @id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ j)ˣ) (a.s j)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ j ⊓ LB.wchart Xo.univ.t.PP.L φ' j' ≤ LB.wchart Xo.univ.t.PP.L φ' j') inf_le_right)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart Xo.univ.t.PP.L φ' j' ≤ ⊤) le_top) v * @id (Γ(Y, LB.wchart Xo.univ.t.PP.L φ' j')ˣ) (b.s j'))
  simp only [map_mul, res_res_lemma]
  rw [H0]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
theorem _root_.solution (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∃ (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1)
      (fun _ => (C.x m).left) fun _ => (1 : ℤ))) (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ),
      (∀ m, (τ m).IsGen) ∧
      (∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m)) ∧
      (∀ m, (u m : Jet S (Fin 1 × Fin (dL Dw)) m) =
        psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))))) ∧
      (∀ m, (eG C φ τ u m).IsGen) ∧ IsExpGaugeOf y C φ (eG C φ τ u) := by
  choose τ hτ hτc using exists_tau C
  choose u hu using exists_uJ C φ hφ
  refine ⟨τ, u, hτ, hτc, hu, fun m => ?_, ?_⟩
  · first
    | exact scaleGen_isGen _ _ _ _ (pullGen_isGen_lemma_4 (hτ m))
    | (unfold eG; exact scaleGen_isGen _ _ _ _ (pullGen_isGen_lemma_4 (hτ m)))
  · first
    | exact fun m => ⟨u m, hu m, corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m))⟩
    | (intro m; exact ⟨u m, hu m, corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m))⟩)
    | (intro m; refine ⟨u m, hu m, ?_⟩; unfold eG; exact corr_scale_lemma_7 (corr_pull_lemma_6 (hτc m)))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
