-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.tyS_Vpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:23.039496+00:00
-- url     : https://prove2.me/submissions/83f6d561-0911-45eb-8958-5eaa8567ac41

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeOfPowEqOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_X_pow_of_not_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
private theorem coeff_tyS_pow_eq_of_two_le {l : ℕ} (hl : 2 ≤ l) (b : ℕ → C) (s : ℕ) :
    PowerSeries.coeff (l ^ s) (tyS l b) = b s := by
  simp only [tyS, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl]
  · intro t _ ht
    rw [if_neg]
    intro e
    exact ht (Nat.pow_right_injective hl e)
  · intro hs
    exfalso
    apply hs
    rw [Finset.mem_range]
    have := Nat.lt_pow_self (by omega : 1 < l) (n := s)
    omega
private theorem coeff_tyS_eq_zero_of_ne_pow {l : ℕ} (b : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) :
    PowerSeries.coeff m (tyS l b) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)
namespace RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
end RawChart
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) :
    tyS l (fun s => if s < 1 then 0 else a (s - 1)) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l a) := by
  have hl0 : 0 < l := by omega
  ext m
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [coeff_subst_X_pow hl0]
    by_cases hk : ∃ t, l ^ t = k
    · obtain ⟨t, rfl⟩ := hk
      rw [← pow_succ', coeff_tyS_pow_eq_of_two_le hl, coeff_tyS_pow_eq_of_two_le hl]
      simp
    · push_neg at hk
      have hk' : ∀ s, l ^ s ≠ l * k := by
        intro s hs
        rcases s with _ | s
        · rw [pow_zero] at hs
          have h1 : l ∣ 1 := ⟨k, hs⟩
          have := Nat.le_of_dvd one_pos h1
          omega
        · rw [pow_succ'] at hs
          exact hk s (Nat.eq_of_mul_eq_mul_left hl0 hs)
      rw [coeff_tyS_eq_zero_of_ne_pow _ _ hk', coeff_tyS_eq_zero_of_ne_pow _ _ hk]
  · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hm]
    simp only [tyS, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs with h1 h2
    · rfl
    · exfalso
      apply hm
      rw [← h1]
      exact dvd_pow_self l (by omega)
    · rfl
end Formalism.L2.FormalSeriesBounds
