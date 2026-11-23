-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.isClosed_upUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:50.270006+00:00
-- url     : https://prove2.me/submissions/ee8cb2d1-2187-4776-8da1-4dd958b33638

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
theorem _root_.solution : IsClosed {x : Matrix (Fin n) (Fin n) K | IsUpUni x} := by
  have hset : {x : Matrix (Fin n) (Fin n) K | IsUpUni x} =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {x | x i j = 0}) ∩ ⋂ a : Fin n, {x | x a a = 1} := by
    ext x
    simp only [IsUpUni, Matrix.IsUpperTriangular, Matrix.BlockTriangular, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter, id]
  rw [hset]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)
end Formalism.DoubleCosetMeasures.P.Supp
