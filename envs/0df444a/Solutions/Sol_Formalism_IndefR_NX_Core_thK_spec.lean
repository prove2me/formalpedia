-- Prove2me | solution 1 for Formalism.IndefR.NX.Core.thK_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:32.886388+00:00
-- url     : https://prove2.me/submissions/99547b49-c489-464f-af84-5f3b8563bd22

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField TensorProduct
open Formalism Formalism.IndefR Formalism.IndefR.NX Formalism.IndefR.NX.Core
attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW
variable (C : RatCore)
namespace Formalism.IndefR.NX.Core
theorem _root_.solution {Dat : Type} (j : ℕ) (σ0 : C.L0 →+* ℂ) (thC : Dat → C.W j σ0) (h : ThExists C j σ0 thC)
    (d : Dat) : IsThOf C j σ0 (thC d) (thK C j σ0 thC h d) :=
  (h d).choose_spec
end Formalism.IndefR.NX.Core
