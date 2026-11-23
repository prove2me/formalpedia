-- Prove2me | solution 1 for Formalism.L2.Th1.H.InterFixed_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:37.389889+00:00
-- url     : https://prove2.me/submissions/9dfb2df9-bf7e-4234-88f7-9ff541f21d3b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Theorems.Thm_Formalism_L2_Th1_H_reps_translate
import Theorems.Thm_Formalism_L2_Th1_H_cosetRepsExist
import Theorems.Thm_Formalism_L2_Th1_H_InterReps_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Reps
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Reps
private theorem semiChar_mul_opU_const_mul_sumU {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ)
    (S : Finset V) (F : V → ℂ) (k : ℂ) (y z : V) :
    α y * opU H y (fun v => k * sumU H α S F v) z
      = k * ∑ x ∈ S, α y * opU H y (fun v => α x * opU H x F v) z := by
  simp only [opU, sumU, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : SemiHom) : InterFixed := by
  intro V _ _ H hH Λ₁ Λ₂ α hα hne F hF
  classical
  obtain ⟨S, hS⟩ := (cosetRepsExist V Λ₁ Λ₂ hne).1
  have hrep := InterReps_of h V H hH Λ₁ Λ₂ α hα F hF
  have hG : inter H α Λ₁ Λ₂ F
      = fun v => ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * sumU H α S F v :=
    funext (hrep S hS)
  show ∀ y ∈ Λ₂, ∀ z, α y * opU H y (inter H α Λ₁ Λ₂ F) z = inter H α Λ₁ Λ₂ F z
  intro y hy z
  calc α y * opU H y (inter H α Λ₁ Λ₂ F) z
      = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
          ∑ x ∈ S, α y * opU H y (fun v => α x * opU H x F v) z := by
        rw [hG]; exact semiChar_mul_opU_const_mul_sumU H α S F _ y z
    _ = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
          ∑ x ∈ S, α (y + x) * opU H (y + x) F z := by
        congr 1
        exact Finset.sum_congr rfl fun x hx => h V H hH Λ₂ α hα y hy x (hS.1 x hx) F z
    _ = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ *
          sumU H α (S.image (fun x => y + x)) F z := by
        congr 1
        unfold sumU
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact add_left_cancel hab
    _ = inter H α Λ₁ Λ₂ F z := (hrep _ (reps_translate hS hy) z).symm
end Formalism.L2.Th1.H
