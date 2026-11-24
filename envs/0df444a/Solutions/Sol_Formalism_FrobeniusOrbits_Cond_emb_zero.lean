-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.emb_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:18:18.672882+00:00
-- url     : https://prove2.me/submissions/4ec485f2-2174-49fa-9191-912074d7b951

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_of_dvd
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_splits_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_sqrt_exists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Cond
section Gauss
variable {K : Type*} [Field K] [CharZero K]
end Gauss
section Cyc
end Cyc
section Div
private theorem X_sq_add_C_natCast_ne_zero (c : ℕ) : (X ^ 2 + C (c : ℚ) : ℚ[X]) ≠ 0 := by
  exact (Polynomial.monic_X_pow_add_C _ two_ne_zero).ne_zero
end Div
section Two
end Two
end Cond
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {q d : ℕ} [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (0 + 2) q d ζ a b)
    {N : ℕ} [NeZero N] (hq : q ∣ N) (hd : d ∣ N) :
    Nonempty (hostE ζ a b →ₐ[ℚ] Cyc N) := by
  have hζ : IsPrimitiveRoot ζ (2 ^ (0 + 2)) := h.1
  have hz2 : ζ ^ 2 = -1 := by
    have h4 : (ζ ^ 2) ^ 2 = 1 := by
      calc (ζ ^ 2) ^ 2 = ζ ^ (2 ^ (0 + 2)) := by ring
        _ = 1 := hζ.pow_eq_one
    have hne : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have h5 : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact absurd (sub_eq_zero.mp h6) hne
    · linear_combination h6
  have hc : ζ + ζ⁻¹ = 0 := by
    have hinv : ζ⁻¹ = -ζ := inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← sq, hz2, neg_neg])
    rw [hinv]
    ring
  have hE : hostE ζ a b = IntermediateField.adjoin ℚ (({a, b} : Set L) ∪ {ζ + ζ⁻¹}) := by
    unfold hostE E0 F1
    rw [IntermediateField.adjoin_union]
  rw [hE]
  obtain ⟨gq, hgq⟩ := sqrt_exists hq4 hq
  obtain ⟨gd, hgd⟩ := sqrt_exists hd4 hd
  apply IntermediateField.nonempty_algHom_adjoin_of_splits
  intro s hs
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with (rfl | rfl) | rfl
  · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero q) (by simp [h.2.1]) (splits_sq q gq hgq)
  · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero d) (by simp [h.2.2.1]) (splits_sq d gd hgd)
  · exact splits_of_dvd _ _ (X_sq_add_C_natCast_ne_zero 0) (by simp [hc]) (splits_sq 0 0 (by simp))
end Formalism.FrobeniusOrbits.Cond
