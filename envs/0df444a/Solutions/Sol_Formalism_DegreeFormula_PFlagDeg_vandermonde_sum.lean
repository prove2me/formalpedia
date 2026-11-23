-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.vandermonde_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:44.690925+00:00
-- url     : https://prove2.me/submissions/09b683ac-8039-4cf4-a8e5-e42d19ca25e2

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg
import Theorems.Thm_Formalism_DegreeFormula_PFlagDeg_pairs_rev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution {N : ℕ} (v : Fin N → ℝ) :
    ∑ s : Equiv.Perm (Fin N), ((Equiv.Perm.sign s : ℤ) : ℝ) *
        ∏ i, v i ^ (N - 1 - ((s i : Fin N) : ℕ)) =
      ∏ i : Fin N, ∏ k : Fin N, if i < k then v i - v k else 1 := by
  rw [pairs_rev, ← Matrix.det_vandermonde,
    ← Matrix.det_submatrix_equiv_self Fin.revPerm (Matrix.vandermonde fun i => v (Fin.rev i)),
    ← Matrix.det_transpose, Matrix.det_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply,
    Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  congr 1
  omega
end Formalism.DegreeFormula.PFlagDeg
