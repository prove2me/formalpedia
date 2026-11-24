-- Prove2me | solution 1 for Formalism.L2.Host.gaussQb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:29.728744+00:00
-- url     : https://prove2.me/submissions/a3188a8c-054d-437b-97e8-008eb489a41b

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (q : ℕ) [Fact q.Prime]
variable {q}
namespace Formalism.L2.Host
theorem _root_.solution {w : Qb} (hw : IsPrimitiveRoot w q) : gaussQb q hw ∈ cycQ q := by
  unfold gaussQb gaussSum
  refine sum_mem fun a _ => mul_mem ?_ ?_
  · show ((quadraticChar (ZMod q) a : ℤ) : Qb) ∈ _
    exact intCast_mem _ _
  · show AddChar.zmodChar q hw.pow_eq_one a ∈ _
    rw [AddChar.zmodChar_apply]
    exact pow_mem (subset_adjoin ℚ (mus q) (show w ∈ mus q from hw.pow_eq_one)) _
end Formalism.L2.Host
