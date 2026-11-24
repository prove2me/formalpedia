-- Prove2me | solution 1 for Formalism.L2.Pj.intFr_of_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:38.814886+00:00
-- url     : https://prove2.me/submissions/14258ed5-59e7-4189-b671-acc721b13a67

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntFrames
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExtPtUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Theorems.Thm_Formalism_L2_Pj_extPt
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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution (hIF : IntFramesSt Xo c) (T : CDVR) (io : c.F →+* T.Fr) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (hPI : PushInvertible Y.t.G Y.t.PP.L) (b : O →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp β) (y₀ : letI := io.toAlgebra; FrPt Xo c T.Fr) :
    ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), (letI := io.toAlgebra; FrBor t y₀ y.1) := by
  letI := io.toAlgebra
  have e1 : y₀.x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y₀.x_over]
    exact spMap_comp _ _
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Sp T.Fr ⟶ pullback Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom),
      z ≫ pullback.fst _ _ = y₀.x ∧ z ≫ pullback.snd _ _ = spMap io :=
    ⟨pullback.lift y₀.x (spMap io) e1, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have e3 : Out.jK T.V = spMap (algebraMap T.V T.Fr) := rfl
  have e4 : Y.j = Y.jQ ≫ pullback.fst _ _ := rfl
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    rw [e4, e3, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hz2,
      ← spMap_comp, ← spMap_comp, hb]
  obtain ⟨yt, hyt1, -⟩ := extPt Y T b z hx
  exact hIF T io O β Y hPI yt z (by rw [← hyt1, e3]) hz2 y₀ hz1.symm
end Formalism.L2.Pj
