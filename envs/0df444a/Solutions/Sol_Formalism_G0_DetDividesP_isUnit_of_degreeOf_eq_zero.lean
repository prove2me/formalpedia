-- Prove2me | solution 1 for Formalism.G0.DetDividesP.isUnit_of_degreeOf_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:23.065813+00:00
-- url     : https://prove2.me/submissions/4cb4b876-73b8-4f70-86b5-ff6256a3e246

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_not_mem_vars_of_degreeOf

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
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {σ : Type} {p : MvPolynomial σ K} (hp : p ≠ 0)
    (h : ∀ x, degreeOf x p = 0) : IsUnit p := by
  have hv : p.vars = ∅ := by
    ext x; simp only [Finset.notMem_empty, iff_false]; exact not_mem_vars_of_degreeOf (h x)
  rw [vars_eq_empty_iff_eq_C] at hv
  rw [hv] at hp ⊢
  have : coeff 0 p ≠ 0 := fun h0 => hp (by rw [h0, map_zero])
  exact (isUnit_iff_ne_zero.mpr this).map C
end Formalism.G0.DetDividesP
