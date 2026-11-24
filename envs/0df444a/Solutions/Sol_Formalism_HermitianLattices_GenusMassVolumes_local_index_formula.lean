-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.local_index_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:08:39.198375+00:00
-- url     : https://prove2.me/submissions/bf7a1b8e-71e0-47ea-9d5e-c79cbef10a59

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_cardGeneralLinear
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_eulerProductBounds
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_half_add_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma triangular_numbers_half (k : ℕ) : ∃ A, k * (k - 1) / 2 = A ∧ k * (k + 1) / 2 = A + k ∧ k * k = 2 * A + k := by
  have hY : k * (k + 1) / 2 = k * (k - 1) / 2 + k := by
    have e : k * (k + 1) = k * (k - 1) + k * 2 := by
      cases k with
      | zero => simp
      | succ n => rw [Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  refine ⟨k * (k - 1) / 2, rfl, hY, ?_⟩
  have := half_add_half k
  rw [hY] at this
  linarith
private lemma odd_square_expansion (k s : ℕ) :
    (k + 2 * s + 1) ^ 2 = k * k + 4 * (s * k) + 4 * (s * s) + 2 * k + 4 * s + 1 := by
  ring
private lemma exponent_square_identities (k s A : ℕ) (hA : k * k = 2 * A + k) :
    ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 = 2 * (s * k) + s + 2 * (s * s) ∧
    ((k + 2 * s + 1) ^ 2 + 3 * k + 1 + 2 * s) / 2 = A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s) := by
  rw [odd_square_expansion, show (k + 1) ^ 2 = k * k + 2 * k + 1 by ring, hA]
  generalize s * k = X
  generalize s * s = Y
  constructor <;> omega
private lemma card_general_linear_group (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) * ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  rw [cardGeneralLinear F n, ← pow_add, half_add_half]
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LocalColumnIndex := by
  intro F _ _ _ k m hm hme hF
  dsimp only
  have hg3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hg0 : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2]
  obtain ⟨hb1, hb2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 k
  obtain ⟨hc1, hc2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 (k + 2 * s + 1)
  refine ⟨⟨_, hb1, hb2, ?_⟩, ⟨_, hc1, hc2, ?_⟩⟩
  · rw [cardGeneralLinear F k, div_eq_iff (pow_ne_zero _ hg0)]
    ring
  · rw [card_general_linear_group F, (exponent_square_identities k s A hA3).1, (exponent_square_identities k s A hA3).2, hA1]
    have hexp : (k + 2 * s + 1) * (k + 2 * s + 1) = (2 * (s * k) + s + 2 * (s * s)) + A +
        (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) := by
      rw [← sq, odd_square_expansion, hA3]
      ring
    rw [hexp, pow_add, pow_add,
      div_eq_iff (mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hg0))]
    ring
end Formalism.HermitianLattices.GenusMassVolumes
