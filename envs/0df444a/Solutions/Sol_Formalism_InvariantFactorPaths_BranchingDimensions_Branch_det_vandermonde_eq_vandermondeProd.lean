-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_vandermonde_eq_vandermondeProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:28.906578+00:00
-- url     : https://prove2.me/submissions/6c1a7172-79c7-413b-9f1c-2645118fe415

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution (n : ℕ) (u : ℕ → ℝ) :
    (Matrix.vandermonde fun i : Fin n => u i).det = W n u := by
  rw [Matrix.det_vandermonde, W,
    Finset.prod_comm' (s' := fun j : Fin n => Iio j) (t' := (univ : Finset (Fin n)))
      (by intro x y; simp),
    ← Fin.prod_univ_eq_prod_range (fun j => ∏ i ∈ range j, (u j - u i)) n]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  rfl
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
