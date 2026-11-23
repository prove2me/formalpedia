-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.psd_off
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:42.860991+00:00
-- url     : https://prove2.me/submissions/13f87893-3f3e-4f03-9629-0edda3d4571f

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_tb_iff_ta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_quad2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psdOn_iff_isPSD
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) {x y : α} (hx : x ∈ F) (hy : y ∈ F) :
    ‖k x y‖ ≤ (k x x).re + (k y y).re := by
  classical
  obtain ⟨ix, rx⟩ := psd_diag hk hx
  obtain ⟨iy, ry⟩ := psd_diag hk hy
  have hn := Complex.norm_le_abs_re_add_abs_im (k x y)
  by_cases hxy : x = y
  · subst hxy
    rw [ix, abs_zero, add_zero, abs_of_nonneg rx] at hn
    linarith
  · have hherm : k y x = conj (k x y) := ((tb_iff_ta F k).1 hk).1 x hx y hy
    have q := fun c : ℂ => ((psdOn_iff_isPSD F k).1 hk (fun u => if u = x then 1 else if u = y then c else 0)).2
    have e := fun c : ℂ => quad2 F k x y hx hy hxy c
    have q1 := q 1
    have q2 := q (-1)
    have q3 := q Complex.I
    have q4 := q (-Complex.I)
    beta_reduce at q1 q2 q3 q4
    rw [e, hherm] at q1 q2 q3 q4
    simp at q1 q2 q3 q4
    have a1 : |(k x y).re| ≤ ((k x x).re + (k y y).re) / 2 := by
      rw [abs_le]; constructor <;> linarith
    have a2 : |(k x y).im| ≤ ((k x x).re + (k y y).re) / 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith
end Formalism.FourierDecayAlt.P.Jx8
