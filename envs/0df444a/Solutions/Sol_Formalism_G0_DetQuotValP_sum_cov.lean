-- Prove2me | solution 1 for Formalism.G0.DetQuotValP.sum_cov
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:37.008394+00:00
-- url     : https://prove2.me/submissions/6f65741d-a6ce-4e41-8584-85f826c756c1

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
import Theorems.Thm_Formalism_G0_DetValP_sum_cov_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetQuotValP
theorem _root_.solution {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) (d : ι → ℕ) (m' : ℕ) :
    ∑ i ∈ S.filter (fun i => vec i = false), (d i + m' * (if i ∈ Set.range A then 1 else 0)) =
      ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cov_zero vec S A hv, mul_zero, add_zero]
end Formalism.G0.DetQuotValP
