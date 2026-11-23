-- Prove2me | solution 1 for Formalism.G0.DetValP.sum_cov_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.337371+00:00
-- url     : https://prove2.me/submissions/29140e89-a926-4642-b4a0-a29cd2fdcb49

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal

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
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]
namespace Formalism.G0.DetValP
theorem _root_.solution {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) :
    ∑ i ∈ S.filter (fun i => vec i = false), (if i ∈ Set.range A then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  have : i ∉ Set.range A := by rintro ⟨l, rfl⟩; simp [hv l] at hi
  simp [this]
end Formalism.G0.DetValP
