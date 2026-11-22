-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx1.conv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:13.134839+00:00
-- url     : https://prove2.me/submissions/668a251b-30f9-4707-ae10-f04a5b979058

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsdFormConjRewrite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx1
namespace Formalism.FourierDecayAlt.P.Jx1
theorem _root_.solution {α : Type} (F : Finset α) (k : α → α → ℂ) (h : TB.PSDOn F k) :
    TA.PSDOn F (fun x y => k y x) := by
  unfold TB.PSDOn at h
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
  obtain ⟨hH, hN⟩ := h
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · have e := hH.apply ⟨y, hy⟩ ⟨x, hx⟩
    simp only [Matrix.of_apply] at e
    show k x y = conj (k y x)
    rw [← e]
    simp
  · have hb := (Complex.le_def.mp (hN (fun i => conj (a i)))).1
    simp only [Complex.zero_re] at hb
    refine le_of_le_of_eq hb ?_
    congr 1
    rw [Finset.sum_comm, ← Finset.sum_coe_sort F]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.star_def, Complex.conj_conj]
    ring
end Formalism.FourierDecayAlt.P.Jx1
