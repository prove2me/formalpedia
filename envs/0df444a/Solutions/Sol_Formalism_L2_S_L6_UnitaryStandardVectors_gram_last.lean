-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.gram_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:53.887871+00:00
-- url     : https://prove2.me/submissions/3ae11d6e-e403-483a-af1c-27dc7f102bac

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Theorems.Thm_Formalism_L2_S_L6_UnitaryStandardVectors_IsUB_zero_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {m : ℕ}
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution {blk : Fin (m + 1) → ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hA : IsUB blk A)
    (Γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hΓ : ∀ i j, (i ≠ Fin.last m ∨ j ≠ Fin.last m) → Γ i j = 0) :
    Aᴴ * Γ * A = Γ := by
  have hrow : ∀ j, A (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    by_cases hj : j = Fin.last m
    · rw [if_pos hj, hj]
      exact hA.1 _
    · rw [if_neg hj]
      exact hA.zero_of_lt (lt_of_le_of_ne (Fin.le_last j) hj)
  ext i j
  simp only [mul_apply, conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [Finset.sum_eq_single (Fin.last m)]
    · rw [hrow i, hrow j]
      by_cases hi : i = Fin.last m
      · by_cases hj : j = Fin.last m
        · subst hi
          subst hj
          simp
        · rw [if_neg hj, hΓ i j (Or.inr hj)]
          simp
      · rw [if_neg hi, hΓ i j (Or.inl hi)]
        simp
    · intro k _ hk
      rw [hΓ k (Fin.last m) (Or.inl hk), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    rw [Finset.sum_eq_zero (fun k _ => by rw [hΓ k l (Or.inr hl), mul_zero]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.L2.S.L6.UnitaryStandardVectors
