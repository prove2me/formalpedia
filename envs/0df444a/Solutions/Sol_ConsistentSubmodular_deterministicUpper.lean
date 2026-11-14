-- Prove2me | solution 1 for ConsistentSubmodular.deterministicUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:28.416588+00:00
-- url     : https://prove2.me/submissions/0d8ef9a3-8cc4-403f-b258-c38372b5c159

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_GridStream_exists_bad_time

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

/-- **Theorem 3** with `K = 6`, on the stream `Σ` with `m = k` stages. -/
theorem deterministicUpper : DeterministicUpperGoal :=
  ⟨6, fun k _ hk hεk _ => ⟨k + k * k, k * k + k * k, gridStreamCover k k,
    exists_bad_time hk le_rfl hεk⟩⟩

end ConsistentSubmodular.GridStream

end

end

section

open ConsistentSubmodular

theorem solution : DeterministicUpperGoal :=
  GridStream.deterministicUpper

end
