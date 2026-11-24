-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.second_capelli_minor_standard_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:11:07.390973+00:00
-- url     : https://prove2.me/submissions/6c02bba9-1985-4f11-a440-c5d724318e5d

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_coefA
import Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_coefB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL
namespace Formalism.FourierDecayAlt.Q.Adapted
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin (n + 2) → Fin (n + 2) → A)
    (u : ℂ) (γ γ' : Fin (n + 2) → ℂ) (hγ : ∀ j : Fin (n + 2), 2 ≤ j.val → γ j = 0 ∧ γ' j = 0) :
    chat2A E u (Pi.single 0 1) (Pi.single 1 1) γ γ' =
      (γ 0 * γ' 1 - γ 1 * γ' 0) • qminor E (skip2 0 1) (skip2 0 1) u := by
  unfold chat2A
  have key : ∀ i i' j j' : Fin (n + 2),
      (if i < i' ∧ j < j' then
        ((-1) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (γ i * γ' i' - γ i' * γ' i) *
          ((Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
            (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j)) •
          qminor E (skip2 i i') (skip2 j j') u
      else 0) =
      if j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0 then (γ 0 * γ' 1 - γ 1 * γ' 0) • qminor E (skip2 0 1) (skip2 0 1) u else 0 := by
    intro i i' j j'
    by_cases h : i < i' ∧ j < j'
    · rw [if_pos h, coefA j j' h.2]
      by_cases hii : i = 0 ∧ i' = 1
      · by_cases hjj : j = 0 ∧ j' = 1
        · obtain ⟨rfl, rfl⟩ := hii
          obtain ⟨rfl, rfl⟩ := hjj
          norm_num
        · rw [if_neg hjj, if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hjj ⟨h'.2.1, h'.1⟩),
            mul_zero, zero_smul]
      · rw [coefB γ γ' hγ i i' h.1 hii,
          if_neg (show ¬(j' = 1 ∧ j = 0 ∧ i' = 1 ∧ i = 0) from fun h' => hii ⟨h'.2.2.2, h'.2.2.1⟩),
          mul_zero, zero_mul, zero_smul]
    · rw [if_neg h, if_neg]
      rintro ⟨rfl, rfl, rfl, rfl⟩
      exact h ⟨by simp [Fin.lt_def], by simp [Fin.lt_def]⟩
  simp only [key]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.FourierDecayAlt.Q.Adapted
