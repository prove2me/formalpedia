-- Prove2me | solution 1 for Formalism.L2.Pj.gfp_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:36:15.692871+00:00
-- url     : https://prove2.me/submissions/8d230c61-3c0a-4d96-920e-3c552a15523f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfV
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenFrPfB
import Theorems.Thm_Formalism_L2_Pj_gfp_bc
import Theorems.Thm_Formalism_L2_Pj_gfp_hcId
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_finrank_eig_bc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_finrank_of_lieMult
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (JetR tvec tmap eigLat IsUnivChart)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {L : Type} [Field L] {x : Sp L ⟶ Xo.X} {n : ℕ}
  {xc : ∀ m : ℕ, ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := L) (JetR L (Fin n) m) ⟶ (Over.pullback x).obj Xo.univ.t.G}
variable [Algebra c.F L]
namespace Formalism.L2.Pj
theorem _root_.solution (hx0 : x ≫ Xo.s = sOf c L) (hx : IsUnivChart _ n xc) (τ : E →+* ℂ) :
    Module.finrank L (gfpEig (c := c) hx τ) = Dw.mult τ := by
  classical
  obtain ⟨xc', hx', -, htm⟩ := gfp_bc (L' := AlgebraicClosure L) hx
  have hrank := ReciprocityTheory.ChartRestriction.G.Chart.finrank_eig_bc (V := L) (k := AlgebraicClosure L)
    (fun a => tmap hx ((Over.pullback x).map (Xo.univ.t.act.act a)))
    (fun a => tmap hx' ((Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a)))
    htm (fun a => algebraMap c.F L (embK c τ a))
  let β : KA l →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp
    ((algebraMap c.F L).comp (IntermediateField.inclusion c.le).toRingHom)
  have hβ : (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) ≫ Xo.s = spMap β := by
    rw [Category.assoc, hx0]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hd := (Xo.univ.geom (AlgebraicClosure L) _ β hβ).1
  let τ' : 𝓞 E →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp ((algebraMap c.F L).comp (embK c τ))
  have key : ∀ N, LieMult Xo.univ.t.act (spMap (algebraMap L (AlgebraicClosure L)) ≫ x) τ' N →
      Module.finrank (AlgebraicClosure L) (eigLat hx'
        (fun a => (Over.pullback (spMap (algebraMap L (AlgebraicClosure L)) ≫ x)).map (Xo.univ.t.act.act a))
        (fun a => τ' a)) = N :=
    fun N h => ReciprocityTheory.ChartRestriction.G.Chart.finrank_of_lieMult gfp_hcId (Category.comp_id _) hx' Xo.univ.t.act
      Xo.univ.t.act.act (fun a => by rw [Category.comp_id, Category.id_comp]) _ (fun a => rfl) τ' h
  have hinj : Function.Injective ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) := RingHom.injective _
  have e0 : τ' H.rt = β (baseKA l).ρ ↔ τ (H.rt : E) = H.rt0 := by
    constructor
    · intro h
      have h' := @hinj (embK c τ H.rt) (IntermediateField.inclusion c.le (baseKA l).ρ) h
      exact congrArg (fun z : c.F => (z : ℂ)) h'
    · intro h
      have h' : embK c τ H.rt = IntermediateField.inclusion c.le (baseKA l).ρ := Subtype.ext h
      exact congrArg ((algebraMap L (AlgebraicClosure L)).comp (algebraMap c.F L)) h'
  refine hrank.trans ?_
  unfold Datum.mult
  split_ifs with h
  · exact key _ ((hd τ').1 (e0.2 h))
  · exact key _ ((hd τ').2 (fun h' => h (e0.1 h')))
end Formalism.L2.Pj
