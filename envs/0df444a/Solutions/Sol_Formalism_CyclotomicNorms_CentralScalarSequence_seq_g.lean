-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:27.377853+00:00
-- url     : https://prove2.me/submissions/8a99c829-658a-4f61-8cd6-840e0d92a999

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
theorem _root_.solution : (fun k => insN 0 a y (k + 1)) = y := by
  funext k; simp [insN]
end Formalism.CyclotomicNorms.CentralScalarSequence
