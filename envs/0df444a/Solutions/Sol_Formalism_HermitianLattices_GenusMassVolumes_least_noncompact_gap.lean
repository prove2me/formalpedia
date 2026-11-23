-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.least_noncompact_gap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:40.852158+00:00
-- url     : https://prove2.me/submissions/acafc87b-9f79-450f-b10d-036b539b7030

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
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
private lemma increments_sum_lower_bound (m : ℕ) (b : ℕ → ℝ) (h₀ : ℝ) (hb : ∀ j, j + 1 < m → h₀ ≤ b (j + 1) - b j)
    (a : ℕ) : ∀ d, a + d < m → (d : ℝ) * h₀ ≤ b (a + d) - b a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := hb (a + d) (by omega)
    rw [← add_assoc]
    push_cast
    linarith
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : LeastNoncompactGap := by
  intro k m v b h₀ hk hh hv hb0 hb i j hij hj hsg
  simp only [plusSign, ne_eq, decide_eq_decide] at hsg
  by_cases hi : i < k - 1
  · by_cases hj' : j < k - 1
    · exact absurd ⟨fun _ => Or.inl hj', fun _ => Or.inl hi⟩ hsg
    · have hodd : (j - (k - 1)) % 2 = 1 := by
        by_contra hc
        exact hsg ⟨fun _ => Or.inr (by omega), fun _ => Or.inl hi⟩
      simp only [rowPar, hi, hj', if_true, if_false]
      have hst := increments_sum_lower_bound m b h₀ hb 0 (j - (k - 1)) (by omega)
      simp only [zero_add] at hst
      have h1 : (1 : ℝ) ≤ ((j - (k - 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - (k - 1))
      have := hv i hi
      nlinarith [mul_le_mul_of_nonneg_right h1 hh]
  · have hj' : ¬ j < k - 1 := by omega
    simp only [rowPar, hi, hj', if_false]
    have hst := increments_sum_lower_bound m b h₀ hb (i - (k - 1)) (j - (k - 1) - (i - (k - 1))) (by omega)
    have e : i - (k - 1) + (j - (k - 1) - (i - (k - 1))) = j - (k - 1) := by omega
    rw [e] at hst
    have h1 : (1 : ℝ) ≤ ((j - (k - 1) - (i - (k - 1)) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ j - (k - 1) - (i - (k - 1)))
    nlinarith [mul_le_mul_of_nonneg_right h1 hh]
end Formalism.HermitianLattices.GenusMassVolumes
