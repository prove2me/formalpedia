-- Prove2me | solution 1 for CubicP3Partition.p12PositionEquiv_symm_inr_one
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T19:55:44.03783+00:00
-- url     : https://prove2.me/submissions/f5ec7fef-59eb-45ba-8da8-5191f1a56857

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

lemma p12PositionEquiv_symm_inr_zero (k : Nat) (i : Fin k) :
    (p12PositionEquiv k).symm (Sum.inr (i, (0 : Fin 2))) = (i, (0 : Fin 3)) := by
  apply (p12PositionEquiv k).injective
  rw [(p12PositionEquiv k).apply_symm_apply]
  simp [p12PositionEquiv]


end
end CubicP3Partition

open CubicP3Partition
universe u
variable {V : Type u}
theorem solution (k : Nat) (i : Fin k) :
    (p12PositionEquiv k).symm (Sum.inr (i, (1 : Fin 2))) = (i, (2 : Fin 3)) := by
  apply (p12PositionEquiv k).injective
  rw [(p12PositionEquiv k).apply_symm_apply]
  simp [p12PositionEquiv]
