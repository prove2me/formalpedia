-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.frob_ser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:53.532876+00:00
-- url     : https://prove2.me/submissions/1984c8c0-78ef-4a75-b4c2-68a152cb0165

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_ge_intCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_valuation_coeff_mul_nonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FrobP_valuation_coeff_pow_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution {A B : PowerSeries C} (hA : ∀ n, V.Ge 0 (PowerSeries.coeff n A))
    (hB : ∀ n, V.Ge 0 (PowerSeries.coeff n B)) (m : ℕ) :
    V.MM (PowerSeries.coeff m ((A + B) ^ V.l - A ^ V.l - B ^ V.l)) := by
  obtain ⟨l', hl'⟩ : ∃ l', V.l = l' + 1 := ⟨V.l - 1, (Nat.succ_pred_eq_of_pos V.l_prime.pos).symm⟩
  have hmid : (A + B) ^ V.l - A ^ V.l - B ^ V.l =
      ∑ i ∈ Finset.range l', ((V.l.choose (i + 1) : ℕ) : C) • (A ^ (i + 1) * B ^ (V.l - (i + 1))) := by
    rw [add_pow, hl', Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.choose_self, Nat.choose_zero_right, Nat.cast_one, mul_one, pow_zero, Nat.sub_self,
      Nat.sub_zero, one_mul]
    have hsm : ∀ i ∈ Finset.range l', A ^ (i + 1) * B ^ (l' + 1 - (i + 1)) *
        (((l' + 1).choose (i + 1) : ℕ) : PowerSeries C) =
        (((l' + 1).choose (i + 1) : ℕ) : C) • (A ^ (i + 1) * B ^ (l' + 1 - (i + 1))) := fun i _ => by
      rw [mul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hsm]
    ring
  rw [hmid, map_sum]
  unfold VF.MM
  refine lt_of_lt_of_le zero_lt_one (AddValuation.map_le_sum _ fun i hi => ?_)
  rw [LinearMap.map_smul, smul_eq_mul, AddValuation.map_mul]
  have hi' := Finset.mem_range.mp hi
  obtain ⟨q, hq⟩ := V.l_prime.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hq' : (((V.l.choose (i + 1)) : ℕ) : C) = (V.l : C) * ((q : ℤ) : C) := by
    rw [hq]
    push_cast
    ring
  rw [hq', AddValuation.map_mul, V.v_l]
  have hqge := ge_intCast (V := V) (q : ℤ)
  have hcoef := valuation_coeff_mul_nonneg (valuation_coeff_pow_nonneg hA (i + 1)) (valuation_coeff_pow_nonneg hB (V.l - (i + 1))) m
  unfold VF.Ge at hqge hcoef
  rw [WithTop.coe_zero] at hqge hcoef
  calc (1 : WithTop ℝ) = 1 + 0 + 0 := by simp
    _ ≤ 1 + V.v ((q : ℤ) : C) + V.v (PowerSeries.coeff m (A ^ (i + 1) * B ^ (V.l - (i + 1)))) :=
      add_le_add (add_le_add le_rfl hqge) hcoef
end Formalism.L2.FormalSeriesBounds.FrobP
