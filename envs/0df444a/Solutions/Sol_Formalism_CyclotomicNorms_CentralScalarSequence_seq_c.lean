-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:26.620813+00:00
-- url     : https://prove2.me/submissions/44cdfbb1-8dbc-4248-9116-254044102196

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
theorem _root_.solution (M i : ℕ) (h : i ≤ M) : contrN (M + 1) (insN i a y) = insN i a (contrN M y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)
end Formalism.CyclotomicNorms.CentralScalarSequence
