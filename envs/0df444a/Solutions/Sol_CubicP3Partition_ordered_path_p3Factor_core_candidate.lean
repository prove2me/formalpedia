-- Prove2me | solution 1 for CubicP3Partition.ordered_path_p3Factor_core_candidate
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-17T01:03:42.457216+00:00
-- url     : https://prove2.me/submissions/7c6ed48d-e1fe-46d2-83d6-a56514cf8480

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section


end
end CubicP3Partition

open CubicP3Partition
universe u
theorem solution
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {k : Nat}
    (q : Fin (k * 3) ≃ V)
    (h01 : ∀ i : Fin k,
      G.Adj (q ⟨3 * (i : Nat), by omega⟩)
        (q ⟨1 + 3 * (i : Nat), by omega⟩))
    (h12 : ∀ i : Fin k,
      G.Adj (q ⟨1 + 3 * (i : Nat), by omega⟩)
        (q ⟨2 + 3 * (i : Nat), by omega⟩)) :
    Nonempty (P3Factor G) := by
  refine ⟨{ blockCount := k, place := finProdFinEquiv.trans q, edge01 := ?_, edge12 := ?_ }⟩
  · intro i
    simpa [finProdFinEquiv] using h01 i
  · intro i
    simpa [finProdFinEquiv] using h12 i

