-- Prove2me | solution 1 for Formalism.L2.Pj.frBorBC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:50.769797+00:00
-- url     : https://prove2.me/submissions/db0d5fc7-bb06-444d-be2c-480b08cad9fc

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_ppx_le_cov
import Theorems.Thm_Formalism_L2_Pj_isCombAt_pull
import Theorems.Thm_Formalism_L2_Pj_scal_pull

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
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution : FrBorBCF Xo c := by
  intro S T _ _ _ _ φ t y y' z z' hb hz hz'
  obtain ⟨hx, hcomb, pmC, hsC, hfC, haC⟩ := hb
  obtain ⟨hx1, hu1, pmA, hsA, hfA, haA⟩ := hz
  obtain ⟨hx2, hu2, pmB, hsB, hfB, haB⟩ := hz'
  have hxz : z'.x = z.x := by rw [hx2, hx1, hx]
  refine ⟨hxz, fun τ i => ?_, ?_⟩
  · obtain ⟨cf, hci, hlow, hc⟩ := hcomb τ i
    refine ⟨fun j => φ (cf j), ?_, fun j hj => by simp only [hlow j hj, map_zero], ?_⟩
    · simp only [hci, Units.coe_map, MonoidHom.coe_coe]
    · exact isCombAt_pull φ.toRingHom hx1 (hu1 τ) (hu2 τ i) hc
  · let pm : Gx z'.x ⟶ Gx z.x :=
      pullback.lift (pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom) (pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom)
        (by
          show pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ z.x =
            pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
          rw [← hxz]
          exact pullback.condition)
    have pfst : pm ≫ pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom :=
      pullback.lift_fst _ _ _
    have psnd : pm ≫ pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom :=
      pullback.lift_snd _ _ _
    have hsA' : pmA ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z.x).hom Xo.univ.t.G.hom := hsA
    have hfA' : pmA ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom =
        pullback.fst (Over.mk z.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfA
    have hsB' : pmB ≫ pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk z'.x).hom Xo.univ.t.G.hom := hsB
    have hfB' : pmB ≫ pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom =
        pullback.fst (Over.mk z'.x).hom Xo.univ.t.G.hom ≫ spMap φ.toRingHom := hfB
    have hsC' : pmC ≫ pullback.snd (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.snd (Over.mk y'.x).hom Xo.univ.t.G.hom := hsC
    have hfC' : pmC ≫ pullback.fst (Over.mk y.x).hom Xo.univ.t.G.hom = pullback.fst (Over.mk y'.x).hom Xo.univ.t.G.hom := hfC
    have hcomp : pm ≫ pmA = pmB ≫ pmC := by
      apply pullback.hom_ext
      · rw [Category.assoc, hfA', ← Category.assoc, pfst, Category.assoc, hfC', hfB']
      · rw [Category.assoc, hsA', psnd, Category.assoc, hsC', hsB']
    refine ⟨pm, psnd, pfst, fun i h => ?_⟩
    have hA := ppx_le_cov pmA hsA i
    have hB' := ppx_le_cov pmB hsB i
    have hC' := ppx_le_cov pmC hsC i
    have key : ∀ (q : Gx z'.x ⟶ Gx y.x), q = pmB ≫ pmC → ∀ hh : (PPx z'.x).U i ≤ q ⁻¹ᵁ (PPx y.x).U i,
        (q.appLE _ _ hh).hom (scal y.x (t none : S) i * y.s.f i) = z'.s.f i := by
      rintro q rfl hh
      have e : (pmB ≫ pmC).appLE _ _ hh = pmC.appLE _ _ hC' ≫ pmB.appLE _ _ hB' :=
        (Scheme.Hom.appLE_comp_appLE pmB pmC _ _ _ hC' hB').symm
      rw [e, CommRingCat.hom_comp, RingHom.comp_apply, haC i hC', haB i hB']
    have e1 : ((Units.map (φ : S →* T) (t none) : Tˣ) : T) = φ.toRingHom (t none : S) := rfl
    show (pm.appLE _ _ h).hom (scal z.x ((Units.map (φ : S →* T) (t none) : Tˣ) : T) i * z.s.f i) = z'.s.f i
    rw [e1, ← haA i hA, ← scal_pull φ.toRingHom pmA hfA i hA, ← map_mul (pmA.appLE _ _ hA).hom]
    have e2 := congrArg (fun f => f.hom (scal y.x (t none : S) i * y.s.f i))
      (Scheme.Hom.appLE_comp_appLE pm pmA _ _ _ hA h)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
    rw [e2]
    exact key _ hcomp _
end Formalism.L2.Pj
