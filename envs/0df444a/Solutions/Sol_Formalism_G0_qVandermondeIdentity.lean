-- Prove2me | solution 1 for Formalism.G0.qVandermondeIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:04.95766+00:00
-- url     : https://prove2.me/submissions/3981cf72-bd37-492f-a141-5319efbda692

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Theorems.Thm_Formalism_G0_QVandermondeP_form2
import Theorems.Thm_Formalism_G0_QVandermondeP_form1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : QVandermonde := fun q m g n =>
  ⟨QVandermondeP.form1 q m g n, QVandermondeP.form2 q m g n⟩
end Formalism.G0
