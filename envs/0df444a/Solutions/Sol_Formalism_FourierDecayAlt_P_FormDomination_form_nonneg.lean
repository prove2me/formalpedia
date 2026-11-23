-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.form_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:22.541708+00:00
-- url     : https://prove2.me/submissions/ae370ebb-96d1-4848-b09f-949d9e699ac7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormDomination
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.FormDomination
theorem _root_.solution {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := (Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  have e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ
      ((Matrix.hadamard (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)).mulVec
        (fun _ => (1 : ℂ))) = ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b := by
    simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
      star_one, one_mul, mul_one]
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort Y]
  rw [e] at H
  exact (Complex.le_def.1 H).1
end Formalism.FourierDecayAlt.P.FormDomination
