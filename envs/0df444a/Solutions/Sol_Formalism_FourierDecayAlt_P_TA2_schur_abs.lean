-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA2.schur_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:31.610105+00:00
-- url     : https://prove2.me/submissions/40e819c3-76fd-407f-a96a-60734b2579e2

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2
namespace Formalism.FourierDecayAlt.P.TA2
theorem _root_.solution {α : Type} (T : Finset α) (c : α → α → ℝ) (A B : α → ℝ) (ep : ℝ)
    (hA : ∀ t ∈ T, 0 ≤ A t) (hB : ∀ t ∈ T, 0 ≤ B t)
    (row : ∀ t ∈ T, ∑ t' ∈ T, c t t' ≤ ep) (col : ∀ t' ∈ T, ∑ t ∈ T, c t t' ≤ ep) :
    ∑ t ∈ T, ∑ t' ∈ T, c t t' * ((A t + B t') / 2)
      ≤ ep * ((∑ t ∈ T, A t + ∑ t ∈ T, B t) / 2) := by
  have e : ∑ t ∈ T, ∑ t' ∈ T, c t t' * ((A t + B t') / 2)
      = (∑ t ∈ T, A t * ∑ t' ∈ T, c t t' + ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t') / 2 := by
    have e2 : ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t' = ∑ t ∈ T, ∑ t' ∈ T, B t' * c t t' := by
      rw [sum_comm]; exact sum_congr rfl fun _ _ => mul_sum _ _ _
    rw [e2, ← sum_add_distrib, sum_div]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum, ← sum_add_distrib, sum_div]
    exact sum_congr rfl fun t' _ => by ring
  rw [e]
  have h1 : ∑ t ∈ T, A t * ∑ t' ∈ T, c t t' ≤ ∑ t ∈ T, A t * ep :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (row t ht) (hA t ht)
  have h2 : ∑ t' ∈ T, B t' * ∑ t ∈ T, c t t' ≤ ∑ t ∈ T, B t * ep :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (col t ht) (hB t ht)
  rw [← sum_mul] at h1 h2
  have e3 : ep * ((∑ t ∈ T, A t + ∑ t ∈ T, B t) / 2)
      = ((∑ t ∈ T, A t) * ep + (∑ t ∈ T, B t) * ep) / 2 := by ring
  rw [e3]; linarith
end Formalism.FourierDecayAlt.P.TA2
