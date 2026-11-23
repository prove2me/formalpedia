-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.thetaSummable_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:56.525927+00:00
-- url     : https://prove2.me/submissions/e0ef5280-6af2-4ff8-bbcc-03df7691db9e

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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) {ι : Type*} [Fintype ι] (e : ι → V) (c : ι → ℤ) :
    Algebra.trace ℚ K (h (∑ i, c i • e i) (∑ i, c i • e i)) =
      ∑ i, ∑ j, (c i : ℚ) * (c j : ℚ) * Algebra.trace ℚ K (h (e i) (e j)) := by
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.HermitianLatticesTheory
