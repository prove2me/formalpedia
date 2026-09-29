-- Prove2me | solution 1 for CubicP3Partition.R03SP01DegreeEqSimpleGraphDegree
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T00:46:28.063908+00:00
-- url     : https://prove2.me/submissions/bb213ba7-984c-41d3-8d72-a33fb823632a

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

set_option maxHeartbeats 1000000


end
end CubicP3Partition

open CubicP3Partition
universe u
theorem solution {X : Type u} [Fintype X]
    (H : SimpleGraph X) (x : X) [DecidableRel H.Adj] :
    CubicP3Partition.degree H x = H.degree x := by
  rw [CubicP3Partition.degree]
  rw [← H.card_neighborSet_eq_degree x]
  exact Nat.card_eq_fintype_card

