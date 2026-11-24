-- Prove2me | solution 1 for Formalism.L2.Pj.isEval_evI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:43.314181+00:00
-- url     : https://prove2.me/submissions/defc0016-bdff-4654-b834-0d20ef56767f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Theorems.Thm_Formalism_L2_Pj_evI_add
import Theorems.Thm_Formalism_L2_Pj_evI_smul
import Theorems.Thm_Formalism_L2_Pj_evI_mul

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
namespace Formalism.L2.Pj
theorem _root_.solution {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) :
    IsEval (W := Unit) (Cusp := fun _ => Rul Xo c) (fun _ _ => ()) (fun _ _ f g => f * g) io
      (fun _ f => evI y f) :=
  ⟨fun _ f g => evI_add y f g, fun _ a f => evI_smul y a f, fun _ _ f g => evI_mul y f g⟩
end Formalism.L2.Pj
