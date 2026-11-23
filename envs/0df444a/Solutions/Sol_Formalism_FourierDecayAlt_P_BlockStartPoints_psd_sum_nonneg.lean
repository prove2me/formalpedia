-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.psd_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:17.799498+00:00
-- url     : https://prove2.me/submissions/c1d53f39-4dae-447b-8261-8ee2ecf27b14

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
theorem _root_.solution {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * g p q).re := by
  have h := (Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  have e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ (Matrix.mulVec (Matrix.hadamard
      (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)) (fun _ => (1 : ℂ))) =
      ∑ p ∈ Y, ∑ q ∈ Y, k p q * g p q := by
    simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
      star_one, one_mul, mul_one]
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_coe_sort Y]
  rw [e] at h
  exact (Complex.le_def.1 h).1
end Formalism.FourierDecayAlt.P.BlockStartPoints
