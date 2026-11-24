-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.hpk_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:46.910361+00:00
-- url     : https://prove2.me/submissions/844f8cb9-fd3a-4d35-8dd3-c2e6a809c230

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq


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
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = sgn k r p * v (sig k r p) := by
  rw [mulVec, dotProduct, Finset.sum_eq_single (sig k r p)]
  · rw [Hpk_eq, if_pos rfl]
  · intro q _ hq; rw [Hpk_eq, if_neg hq, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.QuantumDeterminants.BruhatBigCell
