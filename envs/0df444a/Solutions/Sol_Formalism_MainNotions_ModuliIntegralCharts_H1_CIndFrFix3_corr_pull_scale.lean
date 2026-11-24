-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3.corr_pull_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:00:18.697878+00:00
-- url     : https://prove2.me/submissions/85b1ee7f-4f25-414d-845e-f6eb089e7ae4

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTiePf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_EvalSinglePointId
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
attribute [local instance] Over.cartesianMonoidalCategory
section Alg
variable {S : Type} [CommRing S] {d : ℕ}
end Alg
section Unit
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
variable {O : Type} [CommRing O] [StarRing O]
end Unit
section Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
private theorem app_res_top_lemma {Y Z : Scheme.{0}} (h : Z ⟶ Y) (W : Y.Opens) {W' : Z.Opens}
    (hW : W' ≤ h ⁻¹ᵁ W) (v : Γ(Y, ⊤)) :
    (Z.presheaf.map (homOfLE hW).op).hom ((h.app W).hom ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom v)) =
      (Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op).hom (h.appTop.hom v) := by
  have e : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫ h.app W ≫ Z.presheaf.map (homOfLE hW).op =
      h.appTop ≫ Z.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom v) e
private theorem res_res_top_lemma {X : Scheme.{0}} {V W : X.Opens} (h2 : W ≤ V) (x : Γ(X, ⊤)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res h2 (ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : V ≤ ⊤) x) =
      ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : W ≤ ⊤) x := by
  apply Units.ext
  have e : X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h2).op =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom x.val) e
private theorem pull_res_lemma {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U) {A B : Z.Opens}
    (hA : A ≤ h ⁻¹ᵁ U') (hAB : A ≤ B) (hB : B ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) :
    ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h U' (ReciprocityTheory.ChartRestriction.G.Semi.res hU x)) =
      ReciprocityTheory.ChartRestriction.G.Semi.res hAB (ReciprocityTheory.ChartRestriction.G.Semi.res hB (ReciprocityTheory.ChartRestriction.G.Semi.pullU h U x)) := by
  apply Units.ext
  have e : Y.presheaf.map (homOfLE hU).op ≫ h.app U' ≫ Z.presheaf.map (homOfLE hA).op =
      h.app U ≫ Z.presheaf.map (homOfLE hB).op ≫ Z.presheaf.map (homOfLE hAB).op := by
    rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  exact congrArg (fun f => f.hom x.val) e
end Geo
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
theorem _root_.solution {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ)
    (t t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)) (v : Γ(Y, ⊤)ˣ) (h : Z ⟶ Y)
    (hc : LB.Gen.Corr Xo.univ.t.PP.L φ ε φ ε t (scaleGen φ ε v t')) :
    LB.Gen.Corr Xo.univ.t.PP.L (fun k => h ≫ φ k) ε (fun k => h ≫ φ k) ε (LB.pullGen Xo.univ.t.PP.L φ ε t h)
      (scaleGen (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen Xo.univ.t.PP.L φ ε t' h)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen.Corr at hc ⊢
  intro j j' hj hj' hjj'
  have hc' := hc j j' (fun k₁ k₂ e => hj k₁ k₂ (congrArg (h ≫ ·) e))
    (fun k₁ k₂ e => hj' k₁ k₂ (congrArg (h ≫ ·) e)) (fun k k' e => hjj' k k' (congrArg (h ≫ ·) e))
  have h1 : ∀ i, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) i ≤
      h ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ i :=
    fun i _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hA : ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) j ⊓
      ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L (fun k => h ≫ φ k) j' ≤
      h ⁻¹ᵁ (ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
        ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j') :=
    fun _ hy => And.intro (Set.mem_iInter.2 fun k => Set.mem_iInter.1 (And.left hy) k)
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 (And.right hy) k)
  have key := congrArg (fun (x : Γ(Y, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
      ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j')ˣ) =>
    ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ x)) hc'
  refine Eq.trans ?_ (key.trans ?_)
  · exact (pull_res_lemma h inf_le_left hA inf_le_left (h1 j) (t.s j)).symm
  · simp only [Formalism.L2.Pj.scaleGen]
    erw [map_mul, map_mul, map_mul, map_mul]
    congr 1
    · have s2 : ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _
          (ReciprocityTheory.ChartRestriction.G.Semi.res (le_top : ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
            ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j' ≤ ⊤) v)) =
          ReciprocityTheory.ChartRestriction.G.Semi.res le_top (Units.map h.appTop.hom.toMonoidHom v) :=
        Units.ext (app_res_top_lemma h _ hA v.val)
      refine (congrArg (fun (y : Γ(Y, ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j ⊓
            ReciprocityTheory.ChartRestriction.G.Semi.LB.wchart Xo.univ.t.PP.L φ j')ˣ) =>
          ReciprocityTheory.ChartRestriction.G.Semi.res hA (ReciprocityTheory.ChartRestriction.G.Semi.pullU h _ y))
          (res_res_top_lemma inf_le_right v)).trans ?_
      refine s2.trans ?_
      exact (res_res_top_lemma inf_le_right _).symm
    · exact pull_res_lemma h inf_le_right hA inf_le_right (h1 j') (t'.s j')
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix3
