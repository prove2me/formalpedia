-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.seq_h
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:28.052806+00:00
-- url     : https://prove2.me/submissions/d11c8aef-a11a-4a56-9143-fa5ccc33d3d3

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
theorem _root_.solution (n k : ℕ) (hk : k < n + 1) : contrN (n + 1) (insN (n + 1) a y) k = y k := by
  simp [insN, contrN, hk]
end Formalism.CyclotomicNorms.CentralScalarSequence
