-- Prove2me | solution 1 for Formalism.IndefR.NX.Core.IsThOf.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:09:48.542412+00:00
-- url     : https://prove2.me/submissions/260f6c8d-c258-4362-9472-4f4a8aab5392

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
namespace IsThOf
theorem _root_.solution {j : ℕ} {σ0 : C.L0 →+* ℂ} {thC : C.W j σ0} {x y : C.L0 ⊗[C.Ks] FmK C j}
    (hinj : Function.Injective fun z : C.L0 ⊗[C.Ks] FmK C j => (C.A j).j σ0 (inWL C j z))
    (hx : IsThOf C j σ0 thC x) (hy : IsThOf C j σ0 thC y) : x = y :=
  hinj (hx.trans hy.symm)
end IsThOf
end Formalism.IndefR.NX.Core
