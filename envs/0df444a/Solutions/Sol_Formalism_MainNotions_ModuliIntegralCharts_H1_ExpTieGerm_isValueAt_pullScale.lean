-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm.isValueAt_pullScale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:53.011592+00:00
-- url     : https://prove2.me/submissions/8232f255-54a2-4d60-ab9c-debf1a45c1d4

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieGerm
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieGerm_ptSecT_whisker
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_pullSec_stalk

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
private theorem gs_idRes_lemma {X Y : Scheme.{0}} (h : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    (hV : W ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ W) (x : Γ(X, U)) :
    gs (𝟙 Y) y W ((Y.presheaf.map (homOfLE hV).op).hom ((h.app U).hom x)) = gs h y U x := by
  rw [gs_res (𝟙 Y) y hV hy, gs_pull (𝟙 Y) h y U (hV hy), Category.id_comp]
section Corr
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
end Corr
section Xo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
end Xo
section Pull
variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)
end Pull
section Val
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
end Val
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
theorem _root_.solution (hL : Xo.univ.t.PP.L.IsLB) (a : ℤ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T)} {s' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L a T')}
    (hs : IsPullSec Xo.univ.t.G Xo.univ.t.PP.L a (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) s s')
    {z : T ⟶ Xo.univ.t.G}
    {τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := T.left) (K := Fin 1) (fun _ => z.left) fun _ => a)}
    {v : Γ(T.left, ⊤)} (hv : IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s z τ v) (w : Γ(T'.left, ⊤)ˣ) :
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L a s' (h ≫ z)
      (scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left))
      ((h.left.appTop).hom v * ((w⁻¹ : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤))) := by
  intro j
  apply fn_ext
  intro y hy
  have hy2 : h.left y ∈ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hy3 : (ptSecT Xo.univ.t.G z).left (h.left y) ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L a T).U j :=
    val_le Xo.univ.t.G Xo.univ.t.PP.L z j hy2
  have hy1 : (ptSecT Xo.univ.t.G (h ≫ z)).left y ∈ (LPow Xo.univ.t.G Xo.univ.t.PP.L a T').U j :=
    val_le Xo.univ.t.G Xo.univ.t.PP.L (h ≫ z) j hy
  have hv' : gs h.left y ⊤ v * gs h.left y _ (τ.s j).val =
      gs (h.left ≫ (ptSecT Xo.univ.t.G z).left) y _ (s.f j) := by
    have e := congrArg (gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j)) (hv j)
    rw [gs_mul _ _ _ hy2, gs_res h.left y le_top hy2,
      gs_res h.left y (val_le Xo.univ.t.G Xo.univ.t.PP.L z j) hy2] at e
    exact e.symm.trans (gs_pull h.left (ptSecT Xo.univ.t.G z).left y ((LPow Xo.univ.t.G Xo.univ.t.PP.L a T).U j) hy3
      (s.f j))
  have e1 : gs (𝟙 T'.left) y ⊤ ((h.left.appTop).hom v) = gs h.left y ⊤ v := by
    have := gs_pull (𝟙 T'.left) h.left y ⊤ trivial v
    rw [Category.id_comp] at this
    exact this
  have lhs : gs (𝟙 T'.left) y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j)
      ((T'.left.presheaf.map (homOfLE (val_le Xo.univ.t.G Xo.univ.t.PP.L (h ≫ z) j)).op).hom
        (((ptSecT Xo.univ.t.G (h ≫ z)).left.app _).hom (s'.f j))) =
      gs h.left y ⊤ v * gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (τ.s j).val := by
    refine (gs_idRes_lemma _ _ y hy _).trans ?_
    refine (GermD.pullSec_stalk (A := Xo.univ.t.G) (L := Xo.univ.t.PP.L) a hs _ y j hy1).trans ?_
    rw [ptSecT_whisker Xo.univ.t.G h z]
    exact hv'.symm
  have pgle : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤
      h.left ⁻¹ᵁ LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j :=
    fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k
  have ex2 : (show Γ(T'.left, LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j) from
          ((scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left)).s j).val) =
      (T'.left.presheaf.map (homOfLE (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤)).op).hom
        w.val *
      (T'.left.presheaf.map (homOfLE pgle).op).hom
        ((h.left.app (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j)).hom (τ.s j).val) := rfl
  have rhs : gs (𝟙 T'.left) y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j)
      ((T'.left.presheaf.map (homOfLE (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤)).op).hom
          ((h.left.appTop).hom v * ((w⁻¹ : Γ(T'.left, ⊤)ˣ) : Γ(T'.left, ⊤))) *
        (show Γ(T'.left, LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j) from
          ((scaleGen _ _ w (LB.pullGen Xo.univ.t.PP.L _ _ τ h.left)).s j).val)) =
      gs h.left y ⊤ v * gs h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (τ.s j).val := by
    rw [ex2, map_mul, gs_mul (𝟙 _) y _ hy, gs_mul (𝟙 _) y _ hy, gs_mul (𝟙 _) y _ hy,
      gs_res (𝟙 _) y le_top hy, gs_res (𝟙 _) y le_top hy, gs_res (𝟙 _) y pgle hy]
    erw [gs_pull (𝟙 _) h.left y (LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => z.left) j) (pgle hy)]
    rw [Category.id_comp, e1]
    erw [gs_res (𝟙 _) y (le_top : LB.wchart Xo.univ.t.PP.L (fun _ : Fin 1 => (h ≫ z).left) j ≤ ⊤) hy
      (w : Γ(T'.left, ⊤))]
    rw [gs_unit (𝟙 _) y ⊤ trivial w⁻¹, gs_unit (𝟙 _) y ⊤ trivial w, map_inv,
      mul_assoc (gs h.left y ⊤ v), Units.inv_mul_cancel_left]
  exact lhs.trans rhs.symm
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieGerm
