-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.applicationSteps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:13.364342+00:00
-- url     : https://prove2.me/submissions/791d3a31-2fed-4897-a11d-3e4aa3f99592

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_lastGradedImpliesLast
import Theorems.Thm_P2M_Formalism_CohomologicalDescent_LD_last_graded_implies_one_block__d071e15f0234
import Theorems.Thm_Formalism_CohomologicalDescent_LD_peelRows
import Theorems.Thm_Formalism_CohomologicalDescent_LD_blockStep
import Theorems.Thm_Formalism_CohomologicalDescent_LD_varpi_antitone
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
theorem _root_.solution : ApplicationSteps := by
  intro hD l k j t q h lam hl ht ha hc hh ecl hecl I
  have hP1 := last_graded_implies_one_block' hD
  have hLast := lastGradedImpliesLast hD
  have s3 := peelRows hP1 l k j h lam (fun _ => 0) hl (fun a b hab hb => ha a b hab (by omega)) (by
      have := ha (k + j - 1) (k + j + t + q - 1) (by omega) (by omega)
      omega) (fun _ _ _ => le_rfl) 0 ecl (fun μ _ => hecl μ)
  have s3' : ∀ μ2 : Fin (k + j) → ℕ, ExpLe l (k + j) (res (k + j) lam) μ2 (ecl + j * ((h - 1) / (l - 1))) :=
    fun μ2 => s3 μ2 (by simp [depth2, res])
  have s2 := blockStep hLast l (k + j) t lam hl ht (fun a b hab hb => ha a b hab (by omega)) hc _ s3' I
  have s1 := peelRows hP1 l (k + j + t) q h lam (varpi (k + j)) hl ha hh (varpi_antitone _) I _ s2
  have e : q * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + j * ((h - 1) / (l - 1)) + ecl =
      ecl + j * ((h - 1) / (l - 1)) + blockCost l (k + j) t I lam + q * ((h - 1) / (l - 1)) := by ring
  rw [e]
  exact s1
end Formalism.CohomologicalDescent.LD
