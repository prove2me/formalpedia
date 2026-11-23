-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:26.365428+00:00
-- url     : https://prove2.me/submissions/0747fb6d-6608-4f58-814a-402d413d647e

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
theorem _root_.solution (M j : ℕ) (h : j < M) : contrN j (insN (M + 1) a y) = insN M a (contrN j y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)
end Formalism.CyclotomicNorms.CentralScalarSequence
