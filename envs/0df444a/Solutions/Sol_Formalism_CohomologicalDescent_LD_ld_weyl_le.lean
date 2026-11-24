-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_weyl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:32.606849+00:00
-- url     : https://prove2.me/submissions/982e3a99-b67c-4bba-8e44-0333c29e64a4

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_hw
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_M_gen
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_M_stable
import Theorems.Thm_Formalism_GradedWeylDivisibility_applyWord_cons
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
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y : ℕ) (hy : y ≤ w) : weyl ℤ 2 2 le_rfl (wt2 w y) ≤ ldM w y := by
  unfold weyl
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨wd, rfl⟩
  show applyWord ℤ wd (hw ℤ le_rfl (wt2 w y)) ∈ ldM w y
  induction wd with
  | nil =>
    show hw ℤ le_rfl (wt2 w y) ∈ ldM w y
    rw [ld_hw]
    have := ld_M_gen w y 0 (by omega)
    simpa using this
  | cons x wd ih =>
    rw [applyWord_cons]
    exact ld_M_stable w y _ _ _ _ ih
end Formalism.CohomologicalDescent.LD
