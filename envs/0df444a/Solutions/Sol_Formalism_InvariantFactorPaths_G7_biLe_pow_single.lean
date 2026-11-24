-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biLe_pow_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:40.300432+00:00
-- url     : https://prove2.me/submissions/71c5bb8c-7d37-4ab3-9ed6-9a9435c19bc9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_one

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {x : ι} {W : MvPolynomial κ (MvPolynomial ι K)}
    (h : BiLe (Finsupp.single x 1) W) (m : ℕ) : BiLe (Finsupp.single x m) (W ^ m) := by
  induction m with
  | zero => rw [pow_zero, Finsupp.single_zero]; exact biLe_one
  | succ m ih => rw [pow_succ, Finsupp.single_add]; exact biLe_mul ih h
end Formalism.InvariantFactorPaths.G7
