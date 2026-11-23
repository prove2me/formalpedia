-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.extN_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:25.60706+00:00
-- url     : https://prove2.me/submissions/1ad01251-4afa-46cd-ae8b-ebafa8f92dc9

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
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution {m : ℕ} (x : Fin m → G) : ∀ k : Fin m, x k = extN x k := by
  intro k; simp [extN, k.isLt]
end Formalism.CyclotomicNorms.CentralScalarSequence
