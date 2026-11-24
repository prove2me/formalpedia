-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.det_submatrix_eq_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:08.463071+00:00
-- url     : https://prove2.me/submissions/f7e55456-5046-4ed4-90f9-339b91e5f983

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m m R) (ρ γ : n ≃ m) :
    (A.submatrix ρ γ).det = A.det ∨ (A.submatrix ρ γ).det = -A.det := by
  have e : A.submatrix ρ γ = (A.submatrix ρ ρ).submatrix id (γ.trans ρ.symm) := by
    ext i j
    simp
  rw [e, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (γ.trans ρ.symm)) with h | h <;> rw [h] <;> simp
end Formalism.CohomologicalDescent.LD
