-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.801158+00:00
-- url     : https://prove2.me/submissions/37e3d185-35ca-4302-be0b-80427b62ee12

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementTheta
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ThetaSummable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hpos : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) (x : V) :
    0 ≤ Algebra.trace ℚ K (h x x) := by
  by_cases hx : x = 0
  · subst hx
    simp
  · exact (hpos x hx).le
end Formalism.HermitianLatticesTheory
