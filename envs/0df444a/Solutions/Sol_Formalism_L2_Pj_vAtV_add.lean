-- Prove2me | solution 1 for Formalism.L2.Pj.vAtV_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:46.079267+00:00
-- url     : https://prove2.me/submissions/bb2c040e-bd9b-47c7-91ec-daf48df18147

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Theorems.Thm_Formalism_L2_Pj_evI_add
import Theorems.Thm_Formalism_L2_Pj_nval_add


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c)
variable {Xo c}
variable (Xo c)
variable (cls : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → Prop) (PY : Type)
  (lies : ∀ (T : CDVR) (io : c.F →+* T.Fr), IntFr Xo c T io → PY → Prop)
variable {Xo c cls PY lies}
variable {la : HeightOneSpectrum (𝓞 c.F)}
namespace Formalism.L2.Pj
theorem _root_.solution (y : PtV Xo c cls PY lies la) (f g : Rul Xo c) :
    min (vAtV y f) (vAtV y g) ≤ vAtV y (f + g) := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  show min (nval T.V e (evI y f)) (nval T.V e (evI y g)) ≤ nval T.V e (evI y (f + g))
  rw [evI_add]; exact nval_add e _ _
end Formalism.L2.Pj
