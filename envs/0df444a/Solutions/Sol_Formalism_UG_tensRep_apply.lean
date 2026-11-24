-- Prove2me | solution 1 for Formalism.UG.tensRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:04:12.332178+00:00
-- url     : https://prove2.me/submissions/de5e7fea-8494-4516-b189-50fda2558ae4

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LinSubstIsHomogeneous
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_SatakeDualWeyl_NablaRepApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG
namespace Formalism.UG
theorem _root_.solution (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] (k : ℕ)
    (g : GL n O) : tensRep O n k g = tensAct O n k g := rfl
end Formalism.UG
