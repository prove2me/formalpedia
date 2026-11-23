-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.sgn_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:25.245057+00:00
-- url     : https://prove2.me/submissions/992f00c2-7ff3-434f-9ccd-7d178f70c3c8

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
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.CyclotomicNorms.CentralScalarSequence
theorem _root_.solution (i : ℕ) : (-1 : R) ^ (i + (i + 1)) = -1 := by
  rw [show i + (i + 1) = 2 * i + 1 by ring, pow_succ, pow_mul]; simp
end Formalism.CyclotomicNorms.CentralScalarSequence
