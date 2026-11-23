-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_Hpk_mulVec_lo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:10:38.968426+00:00
-- url     : https://prove2.me/submissions/d0bdec3b-cc19-4669-85c6-c0fc5556029e

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r) : (Hpk k r *ᵥ y) i = y ⟨2 * r + k - i.val, by omega⟩ := by
  rw [gn_Hpk_mulVec, dif_pos (Or.inl hi)]
end Formalism.QuantumDeterminants
