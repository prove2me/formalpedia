-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.rowGenO_comp_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:03.21886+00:00
-- url     : https://prove2.me/submissions/84320a90-f7d0-4798-a380-2041e00a31bf

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
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
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (a b : Fin r) :
    (rowGenO R a b).comp (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))) =
      (Polynomial.mapAlgHom (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n)))).comp
        (rowGen R a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, rename_X, rowGen, rowGenO, aeval_X, Polynomial.coe_mapAlgHom]
  by_cases h1 : v.1 = b <;>
    simp [h1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
end Formalism.GradedWeylDivisibility
