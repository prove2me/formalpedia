-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.third_zeta_position_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:39.402567+00:00
-- url     : https://prove2.me/submissions/e091a4d6-11fe-4e78-9e2c-2da6a9669757

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentFromBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : CoordinatesBoundedByBalance := by
  intro n lam nu X _
  rw [← Finset.sum_add_sum_compl X (fun i => min (len lam i) (B0 lam nu))]
  have h1 : ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ X.card * B0 lam nu := by
    calc ∑ i ∈ X, min (len lam i) (B0 lam nu) ≤ ∑ _i ∈ X, B0 lam nu :=
          Finset.sum_le_sum fun i _ => min_le_right _ _
      _ = X.card * B0 lam nu := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ i ∈ Xᶜ, min (len lam i) (B0 lam nu) ≤ ∑ i ∈ Xᶜ, len lam i :=
    Finset.sum_le_sum fun i _ => min_le_left _ _
  linarith
end Formalism.HermitianLattices.TraceIntegrality
