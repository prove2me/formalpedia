-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.sub_incl_psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:48.317986+00:00
-- url     : https://prove2.me/submissions/39130bf7-ad56-4db7-8eef-7fcc60f8f803

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_not
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_X
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_C
import Theorems.Thm_Formalism_L2_Pj_GenSect_incl_C
import Theorems.Thm_Formalism_L2_Pj_GenSect_X_sub_incl_gs

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
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0) (f : ΩT Ω D m) :
    f - incl j₀ (psi x j₀ f) ∈ Ideal.span (Set.range (sec x)) := by
  have hgen : ∀ p : Fin (D + 1) × Fin m,
      X p - incl j₀ (psi x j₀ (X p)) ∈ Ideal.span (Set.range (sec x)) := by
    intro p
    rw [psi_X]
    by_cases hp : Zs j₀ p
    · obtain ⟨i', j⟩ := p
      have hp' : i' ≠ 0 ∧ j = j₀ := hp
      obtain ⟨i, rfl⟩ : ∃ i : Fin D, i.succ = i' := by
        first
        | exact Fin.exists_succ_eq.mpr hp'.1
        | exact ⟨i'.pred hp'.1, Fin.succ_pred i' hp'.1⟩
      rw [hp'.2, X_sub_incl_gs x j₀ hx₀ i]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · first
      | (rw [gs, if_neg hp, xv_of_not hp, incl, rename_X, sub_self]
         exact Ideal.zero_mem _)
      | simp [gs, hp, xv_of_not hp, incl]
  induction f using MvPolynomial.induction_on
  next a =>
    rw [psi_C, incl_C, sub_self]
    exact Ideal.zero_mem _
  next f g hf hg =>
    have e : f + g - incl j₀ (psi x j₀ (f + g)) =
        (f - incl j₀ (psi x j₀ f)) + (g - incl j₀ (psi x j₀ g)) := by
      simp only [map_add]
      ring
    rw [e]
    exact Ideal.add_mem _ hf hg
  next f p hf =>
    have e : f * X p - incl j₀ (psi x j₀ (f * X p)) =
        (f - incl j₀ (psi x j₀ f)) * X p + incl j₀ (psi x j₀ f) * (X p - incl j₀ (psi x j₀ (X p))) := by
      simp only [map_mul]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (hgen p))
end Formalism.L2.Pj.GenSect
