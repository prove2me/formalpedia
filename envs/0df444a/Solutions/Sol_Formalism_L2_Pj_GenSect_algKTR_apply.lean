-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.algKTR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:28.123901+00:00
-- url     : https://prove2.me/submissions/6fbbe02a-ac3c-49fd-9d39-dd274e380d4f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (q : KT K D m) :
    algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
      algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := by
  exact IsLocalization.map_eq _ _
end Formalism.L2.Pj.GenSect
