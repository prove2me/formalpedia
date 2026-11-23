-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:26.372985+00:00
-- url     : https://prove2.me/submissions/c7b079e9-5ef3-491d-8600-71c0dd134e59

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Central

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.CentralScalarSequence
variable {G : Type} [Group G]
variable (a : G) (y : ℕ → G)
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution (hz : ∀ g, a * g = g * a) (M : ℕ) :
    contrN M (insN (M + 1) a y) = contrN M (insN M a y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega) | (subst_vars; exact (hz _).symm)
end Formalism.CyclotomicNorms.CentralScalarSequence
