-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_vandermonde_eq_ff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:28.910474+00:00
-- url     : https://prove2.me/submissions/5d0f8a40-3422-4d34-88f2-07de8500e6ae

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
theorem _root_.solution {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.vandermonde v).det = (Matrix.of fun i j : Fin n => ff j (v i)).det := by
  rw [Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v (fun j => descPochhammer ℝ j)
    (fun j => descPochhammer_natDegree ℝ j) (fun j => monic_descPochhammer ℝ j)]
  congr 1
  ext i j
  simp only [Matrix.of_apply, descPochhammer_eval_eq_prod_range, ff]
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
