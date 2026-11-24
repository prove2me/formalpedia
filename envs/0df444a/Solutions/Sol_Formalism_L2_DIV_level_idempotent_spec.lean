-- Prove2me | solution 1 for Formalism.L2.DIV.level_idempotent_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:11:00.219163+00:00
-- url     : https://prove2.me/submissions/85f04bb9-26de-4ccb-857d-a2b789fe53f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_gaStar_single
import Theorems.Thm_Formalism_L2_DIV_gaStar_sum
import Theorems.Thm_Formalism_L2_DIV_single_mul_lvlIdem
import Theorems.Thm_Formalism_L2_DIV_lvlIdem_idem
import Theorems.Thm_Formalism_L2_DIV_coeff_lvlIdem
import Theorems.Thm_Formalism_L2_DIV_star_of_pow_eq_one
import Theorems.Thm_Formalism_L2_DIV_mem_cmMax_of_pow_eq_one
import Theorems.Thm_Formalism_L2_DIV_exists_int_of_pow_eq_one
import Theorems.Thm_Formalism_L2_DIV_psi_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : LvlIdemSpec := by
  intro K _ _ _ v0 hv G _ _ P ψ
  classical
  have hcm : ∀ h : P, ((ψ h : Kˣ) : K) ∈ cmMax K :=
    fun h => mem_cmMax_of_pow_eq_one hv Nat.card_pos.ne' (psi_pow P ψ h)
  refine ⟨⟨lvlIdem_idem P ψ, ?_, ?_, ?_⟩, single_mul_lvlIdem P ψ⟩
  · unfold lvlIdem
    rw [gaStar_sum]
    simp only [gaStar_single]
    rw [← Equiv.sum_comp (Equiv.inv P)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Equiv.inv_apply, Subgroup.coe_inv, inv_inv]
    congr 1
    rw [star_mul', star_inv₀, star_natCast, star_of_pow_eq_one hv Nat.card_pos.ne' (psi_pow P ψ k),
      map_inv, Units.val_inv_eq_inv_val]
  · intro t
    rcases coeff_lvlIdem P ψ t with ⟨h, _, ht⟩ | ht
    · rw [ht]
      exact mul_mem (inv_mem (natCast_mem _ _)) (hcm h⁻¹)
    · rw [ht]
      exact zero_mem _
  · intro t
    rcases coeff_lvlIdem P ψ t with ⟨h, _, ht⟩ | ht
    · rw [ht, ← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
      exact exists_int_of_pow_eq_one Nat.card_pos.ne' (psi_pow P ψ h⁻¹)
    · exact ⟨0, by simp [ht]⟩
end Formalism.L2.DIV
