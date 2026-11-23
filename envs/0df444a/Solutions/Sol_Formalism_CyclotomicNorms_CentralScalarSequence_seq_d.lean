-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:27.224044+00:00
-- url     : https://prove2.me/submissions/a41b1eeb-01f1-4a80-9670-1ab33512ee49

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
theorem _root_.solution (i : ℕ) : insN (i + 1) a y 0 = y 0 := by simp [insN]
end Formalism.CyclotomicNorms.CentralScalarSequence
