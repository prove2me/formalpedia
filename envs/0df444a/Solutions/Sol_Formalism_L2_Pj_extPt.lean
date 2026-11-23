-- Prove2me | solution 1 for Formalism.L2.Pj.extPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:39.272286+00:00
-- url     : https://prove2.me/submissions/16a04b85-3553-4138-990b-1840a33e7cd0

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExtPtUnique
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_projProper


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
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace Formalism.L2.Pj
theorem _root_.solution (Y : Model Xo c β) (T : CDVR) (b : O →+* T.V) (x : Sp T.Fr ⟶ Xo.XF c)
    (hx : x ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b) :
    ∃ yt : Sp T.V ⟶ Y.X, Out.jK T.V ≫ yt = x ≫ Y.j ∧ yt ≫ Y.s = spMap b := by
  haveI : IsProper Y.s := projProper _ _ _ Y.proj
  have hE : ValuativeCriterion.Existence Y.s := by
    have h1 : UniversallyClosed Y.s := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h1
    exact h1.1
  let S : ValuativeCommSq Y.s :=
    { R := T.V, K := FractionRing T.V, i₁ := x ≫ Y.j, i₂ := spMap b,
      commSq := ⟨by rw [Category.assoc]; exact hx⟩ }
  obtain ⟨⟨⟨l, hl1, hl2⟩⟩⟩ := hE S
  exact ⟨l, hl1, hl2⟩
end Formalism.L2.Pj
