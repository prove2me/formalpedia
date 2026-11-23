-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.form_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:51.430215+00:00
-- url     : https://prove2.me/submissions/71da6030-75e6-4943-af57-bb2783986786

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_form_nonneg

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
theorem _root_.solution {α ι : Type} (Y : Finset α) (R : Finset ι) (c : ℝ) (k g : α → α → ℂ)
    (Th : ι → α → α → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * k a b - ∑ t ∈ R, Th t a b)) (hg : PSDOn Y g) :
    ∑ t ∈ R, (∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b).re ≤
      c * (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := form_nonneg Y _ g h hg
  have e : ∑ a ∈ Y, ∑ b ∈ Y, ((c : ℂ) * k a b - ∑ t ∈ R, Th t a b) * g a b =
      (c : ℂ) * ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b -
        ∑ t ∈ R, ∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [e, Complex.sub_re, Complex.re_ofReal_mul] at H
  rw [← Complex.re_sum]
  linarith
end Formalism.FourierDecayAlt.P.FormDomination
