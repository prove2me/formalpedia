-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA.eL_isGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:40:10.385688+00:00
-- url     : https://prove2.me/submissions/73b0cf41-a5d9-4693-a529-8a0d9e9dd33a

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen

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
private lemma mulGen_isGen_lemma_5 {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) :
    (LB.mulGen L φ ε φ' ε' t t').IsGen := by
  intro i j
  have Pi : ∀ i', LB.wchart L (Sum.elim φ φ') i' ≤ LB.wchart L φ (i' ∘ Sum.inl) :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k)
  have Qi : ∀ i', LB.wchart L (Sum.elim φ φ') i' ≤ LB.wchart L φ' (i' ∘ Sum.inr) :=
    fun i' _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)
  have H1 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ LB.wchart L φ (i ∘ Sum.inl)) inf_le_left) (@id (Γ(Y, LB.wchart L φ (i ∘ Sum.inl))ˣ) (t.s (i ∘ Sum.inl))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ φ k ⁻¹ᵁ (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ (i ∘ Sum.inl) k)) (inf_le_right.trans (LB.wchart_le L _ (j ∘ Sum.inl) k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ k) (L.U (i (Sum.inl k)) ⊓ L.U (j (Sum.inl k))) (L.g (i (Sum.inl k)) (j (Sum.inl k))))) ^ ε k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) ≤ LB.wchart L φ (j ∘ Sum.inl)) inf_le_right) (@id (Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ) (t.s (j ∘ Sum.inl))) := ht _ _
  have H2 : ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ LB.wchart L φ' (i ∘ Sum.inr)) inf_le_left) (@id (Γ(Y, LB.wchart L φ' (i ∘ Sum.inr))ˣ) (t'.s (i ∘ Sum.inr))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ φ' k ⁻¹ᵁ (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ (i ∘ Sum.inr) k)) (inf_le_right.trans (LB.wchart_le L _ (j ∘ Sum.inr) k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (φ' k) (L.U (i (Sum.inr k)) ⊓ L.U (j (Sum.inr k))) (L.g (i (Sum.inr k)) (j (Sum.inr k))))) ^ ε' k) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) ≤ LB.wchart L φ' (j ∘ Sum.inr)) inf_le_right) (@id (Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ) (t'.s (j ∘ Sum.inr))) := ht' _ _
  have T1 : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ (i ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inl) :=
    inf_le_inf (Pi i) (Pi j)
  have T2 : LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L φ' (i ∘ Sum.inr) ⊓ LB.wchart L φ' (j ∘ Sum.inr) :=
    inf_le_inf (Qi i) (Qi j)
  have G1 := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res T1) H1
  have G2 := congrArg (ReciprocityTheory.ChartRestriction.G.Semi.res T2) H2
  show ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L (Sum.elim φ φ') i) inf_le_left)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi i) (@id (Γ(Y, LB.wchart L φ (i ∘ Sum.inl))ˣ) (t.s (i ∘ Sum.inl))) * ReciprocityTheory.ChartRestriction.G.Semi.res (Qi i) (@id (Γ(Y, LB.wchart L φ' (i ∘ Sum.inr))ˣ) (t'.s (i ∘ Sum.inr)))) =
      (∏ k, (ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ (Sum.elim φ φ' k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
          (le_inf (inf_le_left.trans (LB.wchart_le L _ i k)) (inf_le_right.trans (LB.wchart_le L _ j k))))
        (ReciprocityTheory.ChartRestriction.G.Semi.pullU (Sum.elim φ φ' k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ (Sum.elim ε ε' k)) *
      ReciprocityTheory.ChartRestriction.G.Semi.res (@id (LB.wchart L (Sum.elim φ φ') i ⊓ LB.wchart L (Sum.elim φ φ') j ≤ LB.wchart L (Sum.elim φ φ') j) inf_le_right)
        (ReciprocityTheory.ChartRestriction.G.Semi.res (Pi j) (@id (Γ(Y, LB.wchart L φ (j ∘ Sum.inl))ˣ) (t.s (j ∘ Sum.inl))) * ReciprocityTheory.ChartRestriction.G.Semi.res (Qi j) (@id (Γ(Y, LB.wchart L φ' (j ∘ Sum.inr))ˣ) (t'.s (j ∘ Sum.inr))))
  simp only [map_mul, map_prod, map_zpow, res_res_lemma, Fintype.prod_sum_type] at G1 G2 ⊢
  exact (congrArg₂ (· * ·) G1 G2).trans (mul_mul_mul_comm _ _ _ _)
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
theorem _root_.solution (C : ChartAt Xo c y) (m : ℕ) : (eL y C.d C.x C.B.A.act C.e C.wP m).IsGen := by
  first
  | exact mulGen_isGen_lemma_5 (pullGen_isGen_lemma_4 C.prim.1) (pullGen_isGen_lemma_4 (C.frame.gen m))
  | (dsimp only [Formalism.L2.Pj.eL, Formalism.L2.Pj.pe]
     exact mulGen_isGen_lemma_5 (pullGen_isGen_lemma_4 C.prim.1) (pullGen_isGen_lemma_4 (C.frame.gen m)))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
