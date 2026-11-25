-- Prove2me | solution 1 for Formalism.L2.Pj.arcPt_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:23.758889+00:00
-- url     : https://prove2.me/submissions/ab67041c-5faf-4721-aaba-68ac2dfe531a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArcPtX
import Theorems.Thm_Formalism_L2_Pj_arc_pt_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace Formalism.L2.Pj
theorem _root_.solution (Y : Model Xo c β) {K₁ : Type} [Field K₁] (b : O →+* K₁) [Algebra c.F (ArcS Dw K₁)]
    (hcomp : (algebraMap c.F (ArcS Dw K₁)).comp β = (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp b))
    (χ : Sp (PowerSeries K₁) ⟶ Y.X) (hχs : χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b)
    (hj : ∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧
      z ≫ Y.jQ ≫ pullback.snd _ _ = spMap (algebraMap c.F (ArcS Dw K₁)) := by
  haveI := Y.jQ_open
  have hw : (spMap (arcι Dw K₁) ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcS Dw K₁)) ≫ spMap β := by
    rw [Category.assoc, hχs, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
  let g : Sp (ArcS Dw K₁) ⟶ pullback Y.s (spMap β) :=
    pullback.lift (spMap (arcι Dw K₁) ≫ χ) (spMap (algebraMap c.F (ArcS Dw K₁))) hw
  have hg : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    have e1 : (pullback.fst Y.s (spMap β)) (g q) = χ ((spMap (arcι Dw K₁)) q) := by
      have := congrArg (fun f : Sp (ArcS Dw K₁) ⟶ Y.X => f q) (pullback.lift_fst _ _ hw)
      first
        | exact this
        | (simpa using this)
    show (pullback.fst Y.s (spMap β)) (g q) ∈ abLocus Y.t.G
    rw [e1]
    obtain ⟨p, hp⟩ := hj _ (arc_pt_X Dw K₁ q)
    rw [← hp]
    have h2 : Y.jQ p ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact ⟨p, rfl⟩
    exact h2
  refine ⟨IsOpenImmersion.lift Y.jQ g hg, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ g hg ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]
end Formalism.L2.Pj
