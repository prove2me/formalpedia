-- Prove2me | solution 1 for Formalism.CountingSumsFrames.digit_class_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:21.306525+00:00
-- url     : https://prove2.me/submissions/cb0b089f-2d08-486e-b0e7-0ec9fcf04117

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HockeyStickIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : DigitClassCount := by
  intro m P g hP
  obtain ⟨p, rfl⟩ : ∃ p, P = p + 1 := ⟨P - 1, by omega⟩
  let f : (Fin m → Fin (p + 1)) → Fin (p + 1) := fun τ =>
    ⟨(g + p * digitSum τ) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩
  have hsum : ∀ ρ : Fin (m + 1) → Fin (p + 1),
      (∑ i, (ρ i : ℕ)) = (ρ 0 : ℕ) + digitSum (Fin.tail ρ) := by
    intro ρ
    rw [Fin.sum_univ_succ]
    rfl
  have hcard : (univ : Finset (Fin m → Fin (p + 1))).card = (p + 1) ^ m := by
    simp
  rw [← hcard]
  apply Finset.card_nbij' (fun ρ => Fin.tail ρ) (fun τ => Fin.cons (f τ) τ)
  · intro ρ _
    simp
  · intro τ _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [hsum]
    simp only [Fin.cons_zero, Fin.tail_cons, f]
    rw [Nat.mod_add_mod]
    have : g + p * digitSum τ + digitSum τ = g + (p + 1) * digitSum τ := by ring
    rw [this, Nat.add_mul_mod_self_left]
  · intro ρ hρ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hρ
    rw [hsum] at hρ
    have h0 : f (Fin.tail ρ) = ρ 0 := by
      apply Fin.ext
      simp only [f]
      have hlt : (ρ 0 : ℕ) < p + 1 := (ρ 0).isLt
      have hmod : (ρ 0 : ℕ) + digitSum (Fin.tail ρ) ≡ g [MOD p + 1] := hρ
      have h2 := Nat.ModEq.add_right (p * digitSum (Fin.tail ρ)) hmod
      have h3 : (ρ 0 : ℕ) + digitSum (Fin.tail ρ) + p * digitSum (Fin.tail ρ)
          = (ρ 0 : ℕ) + (p + 1) * digitSum (Fin.tail ρ) := by ring
      rw [h3] at h2
      have h4 : (ρ 0 : ℕ) ≡ g + p * digitSum (Fin.tail ρ) [MOD p + 1] := by
        have h5 : (ρ 0 : ℕ) + (p + 1) * digitSum (Fin.tail ρ) ≡ (ρ 0 : ℕ) [MOD p + 1] := by
          unfold Nat.ModEq
          rw [Nat.add_mul_mod_self_left]
        exact h5.symm.trans h2
      unfold Nat.ModEq at h4
      rw [Nat.mod_eq_of_lt hlt] at h4
      exact h4.symm
    simp only
    rw [h0, Fin.cons_self_tail]
  · intro τ _
    simp
end Formalism.CountingSumsFrames
