-- Prove2me | solution 1 for DetANN.Supplement.Thm32.reps_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T03:40:52.90199+00:00
-- url     : https://prove2.me/submissions/db079e3d-4267-43e6-8232-00be353bc80b

import Mathlib
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_Supplement_PreDedup
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN.HPIM
end DetANN.HPIM
namespace DetANN.HPIM.SegStep
end DetANN.HPIM.SegStep
namespace DetANN.HPIM.PP
end DetANN.HPIM.PP

-- ===== T32_PreParams =====
namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP

/-- With `C₀' = L·τ²/p₀`, `numReps C₀' τ p₀ = L`. -/
lemma numReps_self (L p0 : ℕ) (τ : ℝ) (hτ : 0 < τ) (hp : 0 < p0) :
    numReps ((L : ℝ) * τ ^ 2 / p0) τ p0 = L := by
  unfold numReps
  have hp' : (0 : ℝ) < p0 := by exact_mod_cast hp
  have : (L : ℝ) * τ ^ 2 / p0 * (τ ^ 2)⁻¹ * p0 = L := by field_simp
  rw [this, Nat.ceil_natCast]

/-- `C₀' = L·τ²/p₀ ≥ q` when `q·p₀ ≤ L·τ²`. -/
lemma c0_ge (L p0 : ℕ) (τ q : ℝ) (hp : 0 < p0) (h : q * p0 ≤ L * (τ * τ)) :
    q ≤ (L : ℝ) * τ ^ 2 / p0 := by
  have hp' : (0 : ℝ) < p0 := by exact_mod_cast hp
  rw [le_div_iff₀ hp']; nlinarith

/-- The least power of two `2^m` with `2^m·τ² ≥ c` is at most `max 1 (2c/τ²)`. -/
lemma pow_le_of_least (m : ℕ) (c τ : ℝ) (hτ : 0 < τ)
    (hmin : ∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < c) :
    (2 : ℝ) ^ m ≤ max 1 (2 * c / (τ * τ)) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have h1 := hmin (m - 1) (by omega)
    have hτ2 : 0 < τ * τ := by positivity
    have : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    apply le_max_of_le_right
    rw [this, le_div_iff₀ hτ2]; nlinarith

end DetANN.Supplement.Thm32

-- ===== T32_All =====
namespace DetANN.Supplement.Thm32

open DetANN

lemma reps_facts :
    (∀ (L p0 : ℕ) (τ : ℝ), 0 < τ → 0 < p0 → numReps ((L : ℝ) * τ ^ 2 / p0) τ p0 = L) ∧
    (∀ (L p0 : ℕ) (τ q : ℝ), 0 < p0 → q * p0 ≤ L * (τ * τ) → q ≤ (L : ℝ) * τ ^ 2 / p0) ∧
    (∀ (m : ℕ) (c τ : ℝ), 0 < τ → (∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < c) →
      (2 : ℝ) ^ m ≤ max 1 (2 * c / (τ * τ))) :=
  ⟨numReps_self, c0_ge, pow_le_of_least⟩

end DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

theorem _root_.solution :
    (∀ (L p0 : ℕ) (τ : ℝ), 0 < τ → 0 < p0 → numReps ((L : ℝ) * τ ^ 2 / p0) τ p0 = L) ∧
    (∀ (L p0 : ℕ) (τ q : ℝ), 0 < p0 → q * p0 ≤ L * (τ * τ) → q ≤ (L : ℝ) * τ ^ 2 / p0) ∧
    (∀ (m : ℕ) (c τ : ℝ), 0 < τ → (∀ m' : ℕ, m' < m → 2 ^ m' * (τ * τ) < c) →
      (2 : ℝ) ^ m ≤ max 1 (2 * c / (τ * τ))) :=
  DetANN.Supplement.Thm32.reps_facts

end DetANN.Supplement.Thm32
