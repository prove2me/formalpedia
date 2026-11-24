-- Prove2me | solution 1 for Formalism.L2.Pj.scal_pull
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:52.363626+00:00
-- url     : https://prove2.me/submissions/a59783a5-c90c-4622-8d7b-cf39d17011db

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts

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
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) (a : S) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (φ a) i := by
  have key : ∀ (q : Gx x' ⟶ Sp S), q = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap φ →
      ∀ e : (PPx x').U i ≤ q ⁻¹ᵁ ⊤,
      q.appLE ⊤ ((PPx x').U i) e = (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appLE ⊤ _ (le_top) := by
    rintro q rfl e
    exact Scheme.Hom.comp_appLE _ _ _ _ _
  have M : (fst (Over.mk x) Xo.univ.t.G).left.appTop ≫ (Gx x).presheaf.map (homOfLE le_top).op ≫ pm.appLE _ _ h =
      (spMap φ).appTop ≫ (fst (Over.mk x') Xo.univ.t.G).left.appTop ≫ (Gx x').presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.map_appLE]
    have e1 : (fst (Over.mk x) Xo.univ.t.G).left.appTop =
        (fst (Over.mk x) Xo.univ.t.G).left.appLE ⊤ ⊤ le_top := (Scheme.Hom.appLE_eq_app _).symm
    rw [e1]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans ((key _ hf _).trans rfl)
  have M' := congrArg (fun f => f.hom (toΓ S a)) M
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at M'
  have N := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at N
  show (pm.appLE _ _ h).hom (((Gx x).presheaf.map (homOfLE le_top).op).hom
      ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom (toΓ S a))) =
    ((Gx x').presheaf.map (homOfLE le_top).op).hom ((fst (Over.mk x') Xo.univ.t.G).left.appTop.hom (toΓ T (φ a)))
  rw [M']
  congr 2
  exact N.symm
end Formalism.L2.Pj
