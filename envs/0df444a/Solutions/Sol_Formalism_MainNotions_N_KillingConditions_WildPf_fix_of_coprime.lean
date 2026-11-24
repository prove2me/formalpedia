-- Prove2me | solution 1 for Formalism.MainNotions.N.KillingConditions.WildPf.fix_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:47.609303+00:00
-- url     : https://prove2.me/submissions/a7de89db-e1b3-4884-86ff-aaa2ccb54583

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightVersion_Imports
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_WildPro
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_IsWild_pow
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_val_natCast_eq_one
import Theorems.Thm_Formalism_MainNotions_N_KillingConditions_WildPf_pow_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions Formalism.MainNotions.N.KillingConditions.WildPf
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
variable {A}
namespace Formalism.MainNotions.N.KillingConditions.WildPf
theorem _root_.solution {p m : ℕ} (hpA : A.valuation ((p : ℕ) : Ω) < 1) (hm : Nat.Coprime m p) {τ : Ω ≃ₐ[E] Ω}
    (hτ : IsWild A τ) (y : Ω) (hy : (τ ^ m) y = y) : τ y = y := by
  have hvm := val_natCast_eq_one (A := A) hpA hm
  have hm0 : ((m : ℕ) : Ω) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvm
    exact zero_ne_one hvm
  set T : Ω := ∑ i ∈ Finset.range m, (τ ^ i) y with hT
  have hτT : τ T = T := by
    have h1 : τ T = ∑ i ∈ Finset.range m, (τ ^ (i + 1)) y := by
      rw [hT, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => (τ ^ i) y) m
    have h3 := Finset.sum_range_succ (fun i => (τ ^ i) y) m
    rw [h3, hy] at h2
    have h4 : (τ ^ 0) y = y := rfl
    rw [h4] at h2
    rw [h1]
    exact (add_right_cancel h2).symm
  set z : Ω := (m : Ω) * y - T with hz
  have hzi : ∀ i : ℕ, (τ ^ i) z = (m : Ω) * (τ ^ i) y - T := by
    intro i
    rw [hz, map_sub, map_mul, map_natCast, pow_fix hτT i]
  have hsum : ∑ i ∈ Finset.range m, (τ ^ i) z = 0 := by
    simp only [hzi]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_self]
  have hz0 : z = 0 := by
    by_contra hne
    have h1 : ∑ i ∈ Finset.range m, ((τ ^ i) z / z - 1) = -(m : Ω) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum, zero_div, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one, zero_sub]
    have h2 : A.valuation (∑ i ∈ Finset.range m, ((τ ^ i) z / z - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => (hτ.pow i) z hne
    rw [h1, Valuation.map_neg, hvm] at h2
    exact lt_irrefl _ h2
  have h5 : (m : Ω) * y = T := sub_eq_zero.1 hz0
  have h6 : (m : Ω) * τ y = (m : Ω) * y := by
    rw [h5, ← hτT, ← h5, map_mul, map_natCast]
  exact mul_left_cancel₀ hm0 h6
end Formalism.MainNotions.N.KillingConditions.WildPf
