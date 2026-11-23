-- Prove2me | solution 1 for Formalism.L2.Th1.H.IndexEq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:46.915291+00:00
-- url     : https://prove2.me/submissions/7b5fdb20-60e5-4c7a-a384-2d022bc3468c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Theorems.Thm_Formalism_L2_Th1_H_Inv_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_Inv_altE_neg_right
import Theorems.Thm_Formalism_L2_Th1_H_Inv_sum_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Inv
namespace Formalism.L2.Th1.H
theorem _root_.solution (hc : CharSum) (hr : RepsExist) : IndexEq := by
  intro V _ _ H hH Λ₁ Λ₂ h₁ h₂ h12 h21
  obtain ⟨⟨S₂, hS₂⟩, hcard₂⟩ := hr V Λ₁ Λ₂ h12
  obtain ⟨⟨S₁, hS₁⟩, hcard₁⟩ := hr V Λ₂ Λ₁ h21
  rw [← hcard₂ S₂ hS₂, ← hcard₁ S₁ hS₁]
  have hA : ∑ y ∈ S₂, ∑ x ∈ S₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) = (S₁.card : ℂ) := by
    obtain ⟨y₀, hy₀S, hy₀, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hS₂ (fun y => ∑ x ∈ S₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))) (by
      intro y hy hyn
      rw [hc V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y (hS₂.1 y hy), if_neg hyn])
    rw [hsum, hc V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y₀ (hS₂.1 y₀ hy₀S), if_pos hy₀]
  have hB : ∑ x ∈ S₁, ∑ y ∈ S₂, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H y (-x) : ℂ)) = (S₂.card : ℂ) := by
    obtain ⟨x₀, hx₀S, hx₀, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hS₁ (fun x => ∑ y ∈ S₂, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H y (-x) : ℂ))) (by
      intro x hx hxn
      rw [hc V H hH Λ₂ Λ₁ h₂ h₁ S₂ hS₂ (-x) (Λ₁.neg_mem (hS₁.1 x hx)),
        if_neg (fun h => hxn (by simpa using Λ₂.neg_mem h))])
    rw [hsum, hc V H hH Λ₂ Λ₁ h₂ h₁ S₂ hS₂ (-x₀) (Λ₁.neg_mem (hS₁.1 x₀ hx₀S)), if_pos (Λ₂.neg_mem hx₀)]
  have key : (S₁.card : ℂ) = (S₂.card : ℂ) := by
    rw [← hA, ← hB, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Formalism.L2.Th1.H.Inv.altE_neg_right, Formalism.L2.Th1.H.Inv.altE_swap hH a b, neg_neg]
  exact_mod_cast key.symm
end Formalism.L2.Th1.H
