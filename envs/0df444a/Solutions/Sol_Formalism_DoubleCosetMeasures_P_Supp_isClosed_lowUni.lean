-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.isClosed_lowUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:44.486103+00:00
-- url     : https://prove2.me/submissions/7f0ebe40-d73a-44b0-9115-5224c5f9d91b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
variable {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution : IsClosed {x : Matrix (Fin n) (Fin n) K | IsLowUni x} := by
  have hset : {x : Matrix (Fin n) (Fin n) K | IsLowUni x} =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {x | x i j = 0}) ∩ ⋂ a : Fin n, {x | x a a = 1} := by
    ext x
    simp only [IsLowUni, Matrix.IsLowerTriangular, Matrix.BlockTriangular, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter, OrderDual.toDual_lt_toDual]
  rw [hset]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)
end Formalism.DoubleCosetMeasures.P.Supp
