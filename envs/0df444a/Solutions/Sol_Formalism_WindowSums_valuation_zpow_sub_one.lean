-- Prove2me | solution 1 for Formalism.WindowSums.valuation_zpow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:35.229785+00:00
-- url     : https://prove2.me/submissions/944921d8-88b5-4ef4-a241-0eee04c0fe1c

import Definitions.Def_Formalism_WindowSums_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Theorems.Thm_Formalism_WindowSums_zv_emult_eq_val
import Theorems.Thm_Formalism_WindowSums_zv_emult_unit_mul
import Theorems.Thm_Formalism_WindowSums_zv_pow_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.WindowSums
open Finset
namespace Formalism.WindowSums
theorem _root_.solution : ZpowVal := by
  intro ℓ _ u s hs1 hs2 hval j hj

  have key : ∀ y : ℤ_[ℓ]ˣ, emultiplicity (ℓ : ℤ_[ℓ]) ((y : ℤ_[ℓ]) - 1) = s → ∀ n : ℕ, n ≠ 0 →
      ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 ∧
        PadicInt.valuation (((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s + padicValNat ℓ n := by
    intro y hy n hn
    have hy1 : (ℓ : ℤ_[ℓ]) ∣ (y : ℤ_[ℓ]) - 1 := by
      have h1 := pow_dvd_of_le_emultiplicity (k := 1) (by rw [hy]; exact_mod_cast hs1)
      rwa [pow_one] at h1
    have hy2 : ℓ = 2 → (ℓ : ℤ_[ℓ]) ^ 2 ∣ (y : ℤ_[ℓ]) - 1 := fun h =>
      pow_dvd_of_le_emultiplicity (by rw [hy]; exact_mod_cast hs2 h)
    have he := zv_pow_nat (y : ℤ_[ℓ]) hy1 hy2 hn
    rw [← Units.val_pow_eq_pow_val, hy] at he
    have hne : ((y ^ n : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 ≠ 0 := by
      intro h0
      rw [h0, emultiplicity_zero] at he
      exact absurd he (by norm_cast)
    refine ⟨hne, ?_⟩
    rw [zv_emult_eq_val hne] at he
    exact_mod_cast he
  have hx0 : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hval
    omega
  have hem : emultiplicity (ℓ : ℤ_[ℓ]) ((u : ℤ_[ℓ]) - 1) = s := by
    rw [zv_emult_eq_val hx0, hval]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj rfl
    rw [zpow_natCast, padicValInt.of_nat]
    exact key u hem n hn
  · have hn : n ≠ 0 := by
      rintro rfl
      exact hj (by simp)
    have hinv : emultiplicity (ℓ : ℤ_[ℓ]) (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = s := by
      have e : ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 = (-((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) * ((u : ℤ_[ℓ]) - 1) := by
        rw [mul_sub, neg_mul, Units.inv_mul]
        ring
      rw [e, zv_emult_unit_mul (Units.isUnit _).neg, hem]
    have hv : padicValInt ℓ (-(n : ℤ)) = padicValNat ℓ n := by
      simp [padicValInt]
    rw [zpow_neg, zpow_natCast, ← inv_pow, hv]
    exact key u⁻¹ hinv n hn
end Formalism.WindowSums
