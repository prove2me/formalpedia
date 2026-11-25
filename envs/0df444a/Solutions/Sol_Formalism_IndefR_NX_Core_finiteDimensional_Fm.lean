-- Prove2me | solution 1 for Formalism.IndefR.NX.Core.finiteDimensional_Fm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:17.66591+00:00
-- url     : https://prove2.me/submissions/ee17ee0e-e623-4eae-b118-6cf05d501ba9

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
theorem _root_.solution (i : C.Tw) (j : ℕ) (b : Bool) [FiniteDimensional C.Ks (FmK C j)] :
    FiniteDimensional (FractionRing (C.O i)) (Fm C i j b) :=
  (inferInstance : Module.Finite (KB C i b) (KB C i b ⊗[C.Ks] FmK C j))
end Formalism.IndefR.NX.Core
