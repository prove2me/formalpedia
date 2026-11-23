-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:27.240053+00:00
-- url     : https://prove2.me/submissions/ca360717-7d4c-4522-a1d7-1d2d9c2b0290

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
theorem _root_.solution (i : ℕ) : (fun k => insN (i + 1) a y (k + 1)) = insN i a (fun k => y (k + 1)) := by
  funext k
  simp only [insN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)
end Formalism.CyclotomicNorms.CentralScalarSequence
