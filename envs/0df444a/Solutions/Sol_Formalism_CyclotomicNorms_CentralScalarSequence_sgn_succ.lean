-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CentralScalarSequence.sgn_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:25.498798+00:00
-- url     : https://prove2.me/submissions/e7f09304-ab49-44c0-9b86-8d011899b696

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
theorem _root_.solution (k : ℕ) : (-1 : R) ^ (k + 1) = - (-1 : R) ^ k := by
  rw [pow_succ, mul_neg_one]
end Formalism.CyclotomicNorms.CentralScalarSequence
