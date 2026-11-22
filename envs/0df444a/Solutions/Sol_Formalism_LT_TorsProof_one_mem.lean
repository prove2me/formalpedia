-- Prove2me | solution 1 for Formalism.LT.TorsProof.one_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:23.682284+00:00
-- url     : https://prove2.me/submissions/50bd16cb-4cc7-4c64-b5df-c05783d61be5

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_TorsionNormIterProof

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.LT Formalism.LT.TorsProof
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {π : K} {q : ℕ} {e : Polynomial K}
namespace Formalism.LT.TorsProof
theorem _root_.solution (hπ : 0 < ‖π‖) (he : IsLTPoly q π e) : 1 ∈ Finset.range (e.natDegree + 1) := by
  have : e.coeff 1 ≠ 0 := by
    rw [he.2.1]; intro h; rw [h, norm_zero] at hπ; exact lt_irrefl _ hπ
  exact Finset.mem_range.2 (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero this))
end Formalism.LT.TorsProof
