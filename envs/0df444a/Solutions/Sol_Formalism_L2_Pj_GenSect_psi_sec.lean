-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.psi_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:56.073961+00:00
-- url     : https://prove2.me/submissions/25e55d9a-2349-45e2-a4bf-8c5125143be8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_X
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_C
import Theorems.Thm_Formalism_L2_Pj_GenSect_gs_succ

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
    psi x j₀ (sec x i) = 0 := by
  have hS : (∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) =
      ∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (x k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, ← C_mul, rr]
    congr 2
    first
    | exact div_mul_cancel₀ (x k) hx₀
    | field_simp
  have hI : ∑ j : Fin m, (if j = j₀ then -∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k) else 0) * C (x j) =
      -(∑ k, xv (Ω := Ω) j₀ (i.succ, k) * C (rr x j₀ k)) * C (x j₀) := by
    rw [Finset.sum_eq_single j₀]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  have h1 : psi x j₀ (sec x i) = ∑ j, gs x j₀ (i.succ, j) * C (x j) := by
    simp only [sec, map_sum, map_mul, psi_X, psi_C]
  rw [h1]
  simp only [gs_succ, add_mul]
  rw [Finset.sum_add_distrib, hI, neg_mul, hS]
  first
  | exact add_neg_cancel _
  | exact add_right_neg _
  | abel
end Formalism.L2.Pj.GenSect
