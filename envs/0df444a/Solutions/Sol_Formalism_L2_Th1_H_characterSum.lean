-- Prove2me | solution 1 for Formalism.L2.Th1.H.characterSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:07.466468+00:00
-- url     : https://prove2.me/submissions/e37c2aca-adcb-4994-a5ec-aa43a1d3154d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_SemiCharBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LogarithmEquivalence
import Theorems.Thm_Formalism_L2_Th1_H_Inv_altE_swap
import Theorems.Thm_Formalism_L2_Th1_H_Inv_altE_add_left
import Theorems.Thm_Formalism_L2_Th1_H_Inv_exp_two_pi_int
import Theorems.Thm_Formalism_L2_Th1_H_Inv_int_of_exp_two_pi
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
namespace Inv
variable {V : Type} [AddCommGroup V] [Module ℂ V]
private theorem hermitian_character_exp_add_left (H : Formalism.L2.Th1.H.Sesq V) (u w y : V) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H (u + w) y : ℂ)) = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H u y : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H w y : ℂ)) := by
  rw [altE_add_left, ← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem hermitian_character_exp_eq_one_of_mem_dual_lattice {H : Formalism.L2.Th1.H.Sesq V} (hH : Formalism.L2.Th1.H.IsHerm H) {Λ : AddSubgroup V} {y : V}
    (hy : y ∈ Formalism.L2.Th1.H.dualLat H Λ) {d : V} (hd : d ∈ Λ) : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H d y : ℂ)) = 1 := by
  have hy' : ∀ x ∈ Λ, ∃ m : ℤ, Formalism.L2.Th1.H.altE H y x = m := hy
  obtain ⟨m, hm⟩ := hy' d hd
  have h : Formalism.L2.Th1.H.altE H d y = ((-m : ℤ) : ℝ) := by
    rw [altE_swap hH y d, hm, Int.cast_neg]
  rw [h]
  exact exp_two_pi_int (-m)
private theorem sum_char_isReps_eq_zero_of_nontrivial {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : Formalism.L2.Th1.H.IsReps Λ₂ Λ₁ S)
    (χ : V → ℂ) (hadd : ∀ u w, χ (u + w) = χ u * χ w) (htriv : ∀ d ∈ Λ₂, χ d = 1)
    {x' : V} (hx' : x' ∈ Λ₁) (hne : χ x' ≠ 1) : ∑ x ∈ S, χ x = 0 := by
  classical
  have : Nonempty V := ⟨0⟩
  obtain ⟨hsub, hdist, hcov⟩ := hS
  choose! rep hrepS hrepd using hcov
  have hrep : ∀ v ∈ Λ₁, χ (rep v) = χ v := by
    intro v hv
    have h := hadd (rep v) (v - rep v)
    rw [show rep v + (v - rep v) = v by abel, htriv _ (hrepd v hv), mul_one] at h
    exact h.symm
  have hperm : ∑ x ∈ S, χ (rep (x + x')) = ∑ x ∈ S, χ x := by
    refine Finset.sum_nbij' (i := fun x => rep (x + x')) (j := fun x => rep (x - x')) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact hrepS _ (Λ₁.add_mem (hsub a ha) hx')
    · intro a ha
      exact hrepS _ (Λ₁.sub_mem (hsub a ha) hx')
    · intro a ha
      have h1 : a + x' ∈ Λ₁ := Λ₁.add_mem (hsub a ha) hx'
      have h2 : rep (a + x') - x' ∈ Λ₁ := Λ₁.sub_mem (hsub _ (hrepS _ h1)) hx'
      show rep (rep (a + x') - x') = a
      refine hdist _ (hrepS _ h2) a ha ?_
      have hmem := Λ₂.neg_mem (Λ₂.add_mem (hrepd _ h2) (hrepd _ h1))
      convert hmem using 1
      abel
    · intro a ha
      have h1 : a - x' ∈ Λ₁ := Λ₁.sub_mem (hsub a ha) hx'
      have h2 : rep (a - x') + x' ∈ Λ₁ := Λ₁.add_mem (hsub _ (hrepS _ h1)) hx'
      show rep (rep (a - x') + x') = a
      refine hdist _ (hrepS _ h2) a ha ?_
      have hmem := Λ₂.neg_mem (Λ₂.add_mem (hrepd _ h2) (hrepd _ h1))
      convert hmem using 1
      abel
    · intro a _
      rfl
  have hshift : ∑ x ∈ S, χ (rep (x + x')) = χ x' * ∑ x ∈ S, χ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hrep _ (Λ₁.add_mem (hsub x hx) hx'), hadd, mul_comm]
  have h0 : (1 - χ x') * ∑ x ∈ S, χ x = 0 := by
    rw [sub_mul, one_mul, ← hshift, hperm, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h
end Inv
open Inv
end Formalism.L2.Th1.H
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Inv
namespace Formalism.L2.Th1.H
theorem _root_.solution : CharSum := by
  intro V _ _ H hH Λ₁ Λ₂ h₁ h₂ S hS y hy
  have h₁' : dualLat H Λ₁ = Λ₁ := h₁
  have h₂' : dualLat H Λ₂ = Λ₂ := h₂
  have hy₂ : y ∈ dualLat H Λ₂ := by rw [h₂']; exact hy
  by_cases hy₁ : y ∈ Λ₁
  · rw [if_pos hy₁]
    have hy₁' : y ∈ dualLat H Λ₁ := by rw [h₁']; exact hy₁
    rw [Finset.sum_congr rfl fun x hx => _root_.Formalism.L2.Th1.H.Inv.hermitian_character_exp_eq_one_of_mem_dual_lattice hH hy₁' (hS.1 x hx)]
    simp
  · rw [if_neg hy₁]
    have hy₁' : y ∉ dualLat H Λ₁ := by rw [h₁']; exact hy₁
    have hx' : ∃ x' ∈ Λ₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x' y : ℂ)) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      apply hy₁'
      show ∀ x ∈ Λ₁, ∃ m : ℤ, altE H y x = m
      intro x hx
      obtain ⟨m, hm⟩ := Formalism.L2.Th1.H.Inv.int_of_exp_two_pi (hcon x hx)
      exact ⟨-m, by rw [Formalism.L2.Th1.H.Inv.altE_swap hH x y, hm, Int.cast_neg]⟩
    obtain ⟨x', hx'Λ, hne⟩ := hx'
    exact _root_.Formalism.L2.Th1.H.Inv.sum_char_isReps_eq_zero_of_nontrivial hS (fun v => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H v y : ℂ))) (fun u w => _root_.Formalism.L2.Th1.H.Inv.hermitian_character_exp_add_left H u w y)
      (fun d hd => _root_.Formalism.L2.Th1.H.Inv.hermitian_character_exp_eq_one_of_mem_dual_lattice hH hy₂ hd) hx'Λ hne
end Formalism.L2.Th1.H
