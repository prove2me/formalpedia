-- Prove2me | solution 1 for ConsistentSubmodular.prefixBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:44.620347+00:00
-- url     : https://prove2.me/submissions/03df727d-0e95-49de-97ce-91de69516491

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds
import Theorems.Thm_ConsistentSubmodular_WindowInstance_prefix_bound

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace Certificates

/-- Lemma B.5 (prefix bound). -/
theorem prefixBound : PrefixBoundGoal := by
  intro n W j c hjc
  have h := W.prefix_bound hjc
  change 4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c ≤
    4 * W.pairValue j 0 c (1 / 2) at h
  unfold WindowInstance.pairValue at h
  linarith

end Certificates

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution : PrefixBoundGoal :=
  Certificates.prefixBound

end
