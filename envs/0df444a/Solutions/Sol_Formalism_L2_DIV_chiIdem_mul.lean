-- Prove2me | solution 1 for Formalism.L2.DIV.chiIdem_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:55:31.234991+00:00
-- url     : https://prove2.me/submissions/a8f820d9-d6a6-4ad2-8a6f-9d8ec2713eaf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_coeff_mul_fin
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_conj
import Theorems.Thm_Formalism_L2_DIV_coeff_chiIdem
import Theorems.Thm_Formalism_L2_DIV_conv_char

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
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical
namespace Formalism.L2.DIV
theorem _root_.solution {χ χ' : G → K} (h : IsAbsIrrChar χ) (h' : IsAbsIrrChar χ') :
    chiIdem χ * chiIdem χ' = if χ = χ' then chiIdem χ' else 0 := by
  classical
  have hn : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext u
  rw [coeff_mul_fin]
  simp only [coeff_chiIdem]
  have hs : ∑ s : G, χ 1 / (Fintype.card G : K) * χ s⁻¹ * (χ' 1 / (Fintype.card G : K) * χ' (s⁻¹ * u)⁻¹) =
      χ 1 / (Fintype.card G : K) ^ 2 * ((∑ s, χ s⁻¹ * χ' (s * u⁻¹)) * χ' 1) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_inv_rev, inv_inv, show χ' (u⁻¹ * s) = χ' (s * u⁻¹) from ?_]
    · ring
    · rw [← h'.conj s (u⁻¹ * s)]
      congr 1
      group
  rw [hs, conv_char h h' u⁻¹]
  split_ifs with he
  · subst he
    rw [coeff_chiIdem]
    field_simp
    try ring
  · rw [mul_zero]
    simp
end Formalism.L2.DIV
