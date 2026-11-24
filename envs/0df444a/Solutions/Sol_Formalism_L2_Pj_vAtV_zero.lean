-- Prove2me | solution 1 for Formalism.L2.Pj.vAtV_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:23:09.185678+00:00
-- url     : https://prove2.me/submissions/c1d8b78a-94ea-4d98-80cc-838410b6999b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Theorems.Thm_Formalism_L2_Pj_isEval_evI
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero
import Theorems.Thm_Formalism_L2_Pj_nval_zero


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
theorem _root_.solution (y : PtV Xo c cls PY lies la) : vAtV y 0 = ⊤ := by
  rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
  show nval T.V e (evI y 0) = ⊤
  rw [(isEval_evI y).zero (), nval_zero]
end Formalism.L2.Pj
