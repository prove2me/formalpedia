-- Prove2me | solution 1 for Formalism.L2.Pj.frMap_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:59.018539+00:00
-- url     : https://prove2.me/submissions/2a3cb125-cbab-4008-9785-2f24d468dd32

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_spMap_algHom_comp
import Theorems.Thm_Formalism_L2_Pj_spMap_dual_comp
import Theorems.Thm_Formalism_L2_Pj_ppx_le_cov

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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
variable {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution : MapCancel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) := by
  intro S T U _ _ _ _ _ _ φ ψ y z w h₁ h₂
  obtain ⟨hx1, hu1, pm1, hs1, hf1, ha1⟩ := h₁
  obtain ⟨hx2, hu2, pm2, hs2, hf2, ha2⟩ := h₂
  have hxw : w.x = spMap ψ.toRingHom ≫ z.x := by
    rw [hx2, hx1, spMap_algHom_comp, Category.assoc]
  let pm : Gx w.x ⟶ Gx z.x :=
    pullback.lift (pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap ψ.toRingHom) (pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap ψ.toRingHom ≫ z.x = pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hxw]
        exact pullback.condition)
  have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap ψ.toRingHom :=
    pullback.lift_fst _ _ _
  have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom :=
    pullback.lift_snd _ _ _
  have hs1' : pm1 ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hs1
  have hf1' : pm1 ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hf1
  have hs2' : pm2 ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk w.x).hom Xo.univ.t.G.hom := hs2
  have hf2' : pm2 ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
      pullback.fst (Over.mk w.x).hom Xo.univ.t.G.hom ≫ spMap (ψ.comp φ).toRingHom := hf2
  have hcomp : pm ≫ pm1 = pm2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hf1', ← Category.assoc, pfst, hf2', spMap_algHom_comp, Category.assoc]
    · rw [Category.assoc, hs1', psnd, hs2']
  refine ⟨hxw, ?_, pm, psnd, pfst, ?_⟩
  · intro τ i
    rw [hu2 τ i, hu1 τ i, spMap_dual_comp, Category.assoc]
  · intro i h
    have h1' := ppx_le_cov pm1 hs1 i
    have key : ∀ (q : Gx w.x ⟶ Gx y.x), q = pm2 → ∀ hh : (PPx w.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
        (q.appLE _ _ hh).hom (y.s.f i) = w.s.f i := by
      rintro q rfl hh
      exact ha2 i hh
    have e := (Scheme.Hom.appLE_comp_appLE pm pm1 _ _ _ h1' h).symm
    rw [← ha1 i h1', ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e]
    exact key _ hcomp _
end Formalism.L2.Pj
