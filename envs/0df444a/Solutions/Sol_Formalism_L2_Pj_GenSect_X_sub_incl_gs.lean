-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.X_sub_incl_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:50.643268+00:00
-- url     : https://prove2.me/submissions/e6e2e9a6-a7f1-4d54-a0d0-f11f6374e492

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_incl_C
import Theorems.Thm_Formalism_L2_Pj_GenSect_incl_xv_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (i : Fin D) :
    X (i.succ, j₀) - incl j₀ (gs x j₀ (i.succ, j₀)) = C (x j₀)⁻¹ * sec x i := by
  have hz : Zs j₀ (i.succ, j₀) := by
    unfold Zs
    exact ⟨Fin.succ_ne_zero i, rfl⟩
  rw [gs, if_pos hz]
  simp only [map_neg, map_sum, map_mul, incl_C, incl_xv_succ, sub_neg_eq_add, sec, Finset.mul_sum]
  have hX : (X (i.succ, j₀) : ΩT Ω D m) = ∑ j : Fin m, if j = j₀ then (X (i.succ, j₀) : ΩT Ω D m) else 0 := by
    simp
  rw [hX, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = j₀
  · subst h
    rw [if_pos rfl, if_pos rfl, zero_mul, add_zero, mul_left_comm, ← C_mul, inv_mul_cancel₀ hx₀, C_1, mul_one]
  · rw [if_neg h, if_neg h, zero_add, rr, div_eq_mul_inv, C_mul]
    ring
end Formalism.L2.Pj.GenSect
