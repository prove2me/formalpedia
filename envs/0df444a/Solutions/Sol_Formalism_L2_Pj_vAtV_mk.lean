-- Prove2me | solution 1 for Formalism.L2.Pj.vAtV_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:56.96846+00:00
-- url     : https://prove2.me/submissions/bc8eaf1d-9163-4d28-80ef-b17eab9cdb4e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot

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
namespace Formalism.L2.Pj
theorem _root_.solution (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa la T.V io e) (y : IntFr Xo c T io) (hy : cls T io y) (eta : PY) (heta : lies T io y eta)
    (f : Rul Xo c) : vAtV (PtV.mk la ho y hy eta heta) f = nval T.V e (evI y f) := rfl
end Formalism.L2.Pj
