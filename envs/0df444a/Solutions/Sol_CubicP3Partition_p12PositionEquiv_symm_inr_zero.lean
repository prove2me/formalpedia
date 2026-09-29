-- Prove2me | solution 1 for CubicP3Partition.p12PositionEquiv_symm_inr_zero
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T10:13:26.333115+00:00
-- url     : https://prove2.me/submissions/28365491-6bd1-4eef-ab7a-b59452a8d774

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_5719a22c9e_R03CenterHall

/-!
# R03 center--Hall equivalence

For a finite graph, a P3 factor is equivalent to a finite center set of one
third of the vertices whose external neighborhood satisfies the two-fold Hall
inequality.  The proof uses a duplicated-center Hall matching; no cubicity or
connectivity assumption is needed for this equivalence.
-/

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}

end
end CubicP3Partition

open CubicP3Partition
universe u
variable {V : Type u}
theorem solution (k : Nat) (i : Fin k) :
    (p12PositionEquiv k).symm (Sum.inr (i, (0 : Fin 2))) = (i, (0 : Fin 3)) := by
  apply (p12PositionEquiv k).injective
  rw [(p12PositionEquiv k).apply_symm_apply]
  simp [p12PositionEquiv]
