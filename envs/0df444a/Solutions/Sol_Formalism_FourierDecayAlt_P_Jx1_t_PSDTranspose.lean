-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.t_PSDTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:28.428236+00:00
-- url     : https://prove2.me/submissions/2f2f8c18-ba5d-4ade-b683-78aa9ff5fa1c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx1_conv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.Jx1
private theorem im_quadratic_form_eq_zero_of_hermitian {α : Type} (F : Finset α) (k : α → α → ℂ)
    (hh : ∀ x ∈ F, ∀ y ∈ F, k y x = conj (k x y)) (a : α → ℂ) :
    (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y).im = 0 := by
  have h : conj (∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun v hv => ?_
    rw [← hh v hv u hu]
    ring
  exact Complex.conj_eq_iff_im.mp h
private theorem tb_psdOn_of_ta_psdOn {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TA.PSDOn F k) :
    TB.PSDOn F k := by
  classical
  unfold TB.PSDOn
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply]
    rw [h.1 i i.2 j j.2]
    simp
  · set a : α → ℂ := fun u => if hu : u ∈ F then x ⟨u, hu⟩ else 0 with ha
    have hQ : star x ⬝ᵥ (Matrix.of fun u v : F => k u v).mulVec x =
        ∑ u ∈ F, ∑ v ∈ F, conj (a u) * k u v * a v := by
      rw [← Finset.sum_coe_sort F]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_coe_sort F]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [ha, Complex.star_def, mul_assoc]
    rw [hQ, Complex.le_def]
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨h.2 a, (im_quadratic_form_eq_zero_of_hermitian F k h.1 a).symm⟩
section Tower
variable {E : Type} [Field E]
end Tower
section Agree
variable {α : Type}
end Agree
end Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution : PSDTranspose := by
  unfold PSDTranspose
  intro α F k h
  exact tb_psdOn_of_ta_psdOn F _ (conv F k h)
end Formalism.FourierDecayAlt.P.Jx1
