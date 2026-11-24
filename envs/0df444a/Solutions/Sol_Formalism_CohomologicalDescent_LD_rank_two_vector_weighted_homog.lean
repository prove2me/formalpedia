-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rank_two_vector_weighted_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:09.783811+00:00
-- url     : https://prove2.me/submissions/eae3e48f-0e16-4f81-8d18-0e5df9ed0d05

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rank_two_vector_def
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
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
theorem _root_.solution (w y i : ℕ) (h : y + i ≤ w) :
    IsWeightedHomogeneous (rowW 2 2) (vec2 w y i) (wt2 (w - i) (y + i)) := by
  rw [rank_two_vector_def]
  have hX : ∀ a b : Fin 2, IsWeightedHomogeneous (rowW 2 2)
      (X (a, b) : MvPolynomial (Fin 2 × Fin 2) ℤ) (Pi.single a 1) :=
    fun a b => isWeightedHomogeneous_X _ _ _
  have hD : IsWeightedHomogeneous (rowW 2 2) ldDet (Pi.single 0 1 + Pi.single 1 1) := by
    have h1 := (hX 0 0).mul (hX 1 1)
    have h2 := (hX 0 1).mul (hX 1 0)
    rw [← mem_weightedHomogeneousSubmodule] at h1 h2 ⊢
    exact Submodule.sub_mem _ h1 h2
  have hall := (((hX 0 0).pow (w - y - i)).mul ((hX 1 0).pow i)).mul (hD.pow y)
  convert hall using 1
  funext a
  fin_cases a <;> simp [wt2] <;> omega
end Formalism.CohomologicalDescent.LD
