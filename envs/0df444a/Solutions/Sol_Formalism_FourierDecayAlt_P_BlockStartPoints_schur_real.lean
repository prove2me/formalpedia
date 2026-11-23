-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.schur_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:18.186831+00:00
-- url     : https://prove2.me/submissions/13a7105e-e044-4223-8e61-c77803acf0e0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution {τ : Type} (S : Finset τ) (m : τ → τ → ℝ) (ep M : ℝ) (hep : 0 ≤ ep)
    (row : ∀ t ∈ S, ∑ t' ∈ S, m t t' ≤ ep) (col : ∀ t' ∈ S, ∑ t ∈ S, m t t' ≤ ep)
    (a b : τ → ℝ) (ha : ∀ t, 0 ≤ a t) (hb : ∀ t, 0 ≤ b t)
    (hA : ∑ t ∈ S, a t ≤ M) (hB : ∑ t ∈ S, b t ≤ M) :
    ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a t + b t') / 2) ≤ ep * M := by
  have e : ∑ t ∈ S, ∑ t' ∈ S, m t t' * ((a t + b t') / 2) =
      (∑ t ∈ S, a t * ∑ t' ∈ S, m t t') / 2 + (∑ t' ∈ S, b t' * ∑ t ∈ S, m t t') / 2 := by
    have e2 : ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' = ∑ t ∈ S, ∑ t' ∈ S, b t' * m t t' := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun t' _ => Finset.mul_sum _ _ _
    rw [e2, ← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun t' _ => by ring
  rw [e]
  have h1 : ∑ t ∈ S, a t * ∑ t' ∈ S, m t t' ≤ ep * M := by
    calc ∑ t ∈ S, a t * ∑ t' ∈ S, m t t' ≤ ∑ t ∈ S, a t * ep :=
          Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (row t ht) (ha t)
      _ = ep * ∑ t ∈ S, a t := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ ep * M := mul_le_mul_of_nonneg_left hA hep
  have h2 : ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' ≤ ep * M := by
    calc ∑ t' ∈ S, b t' * ∑ t ∈ S, m t t' ≤ ∑ t' ∈ S, b t' * ep :=
          Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left (col t ht) (hb t)
      _ = ep * ∑ t ∈ S, b t := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ ep * M := mul_le_mul_of_nonneg_left hB hep
  linarith
end Formalism.FourierDecayAlt.P.BlockStartPoints
