-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.frob2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:59.502045+00:00
-- url     : https://prove2.me/submissions/d1cf72ee-4dbf-46b1-b7ce-ece5c87be37a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_mul_int
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

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
namespace ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
private theorem v_natCast_nonneg' (n : ℕ) : 0 ≤ V.v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (V.v.map_add _ _)
    rw [V.v.map_one]
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
end ValuationNonnegativity
section Closed
variable {C : Type} [Field C]
end Closed
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ V.l - a ^ V.l - b ^ V.l) := by
  have hl := V.l_prime
  obtain ⟨k, hk⟩ : ∃ k, V.l = k + 2 := ⟨V.l - 2, by have := hl.two_le; omega⟩
  have hl' : (k + 2).Prime := hk ▸ hl
  have hint : ∀ m n : ℕ, V.Ge 0 (a ^ m * b ^ n) := by
    intro m n
    rw [valuation_nonneg_iff, V.v.map_mul, V.v.map_pow, V.v.map_pow]
    exact add_nonneg (nsmul_nonneg (valuation_nonneg_iff.mp ha) m) (nsmul_nonneg (valuation_nonneg_iff.mp hb) n)
  have hch : ∀ m ∈ Finset.range (k + 1),
      V.MM (a ^ (m + 1) * b ^ (k + 2 - (m + 1)) * ((k + 2).choose (m + 1) : C)) := by
    intro m hm
    rw [Finset.mem_range] at hm
    apply mm_mul_int (hint _ _)
    obtain ⟨t, ht⟩ : (k + 2) ∣ (k + 2).choose (m + 1) := hl'.dvd_choose_self (by omega) (by omega)
    rw [ht, Nat.cast_mul, ← hk]
    unfold VF.MM
    rw [V.v.map_mul, V.v_l]
    exact lt_of_lt_of_le (by exact_mod_cast one_pos) (le_add_of_nonneg_right (v_natCast_nonneg' t))
  have hexp : (a + b) ^ V.l - a ^ V.l - b ^ V.l =
      ∑ m ∈ Finset.range (k + 1), a ^ (m + 1) * b ^ (k + 2 - (m + 1)) * ((k + 2).choose (m + 1) : C) := by
    rw [hk, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, mul_one, Nat.sub_zero, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, Nat.sub_self]
    ring
  rw [hexp]
  exact mm_sum hch
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
