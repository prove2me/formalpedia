-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ndEul_homog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:09.126842+00:00
-- url     : https://prove2.me/submissions/1c6f6c0c-4f5c-4866-bf04-49e2c2239a43

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LNondomLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_nd_weight_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_ndEul_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
set_option linter.unusedSimpArgs false
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {g : MvPolynomial (Fin r × Fin n) R} {μ : Fin n → ℕ}
    (hg : IsWeightedHomogeneous (colW r n) g μ) (s : Fin n) :
    ndEul R r n s g = (μ s : R) • g := by
  ext m
  rw [ndEul_coeff, coeff_smul, smul_eq_mul]
  by_cases h : coeff m g = 0
  · simp [h]
  · rw [nd_weight_apply, hg h]
end Formalism.GradedWeylDivisibility
