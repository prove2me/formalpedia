-- Prove2me | solution 1 for Formalism.CyclotomicNorms.low_degree_power_series
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:40.722898+00:00
-- url     : https://prove2.me/submissions/58d7d505-c83c-479a-bdf0-eadb51a2e4d9

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_LowDegreePowerSeries
import Theorems.Thm_Formalism_CyclotomicNorms_low_key
import Theorems.Thm_Formalism_CyclotomicNorms_low_coeff_dvd
import Theorems.Thm_Formalism_CyclotomicNorms_low_divide

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.CyclotomicNorms
namespace Formalism.CyclotomicNorms
theorem _root_.solution : LowPowerSeries := by
  intro O _ _ _ ϖ n m₀ D g hϖ hord hg hmem
  set Db := PowerSeries.map (IsLocalRing.residue O) D with hDb
  have hne : Db ≠ 0 := by
    intro h
    rw [h, order_zero] at hord
    exact absurd hord (by simp)
  set m := Db.order.toNat with hm
  have hmm : m ≤ m₀ := by
    have := coe_toNat_order hne
    rw [← this] at hord
    exact_mod_cast hord
  set U : PowerSeries O := mk fun k => coeff (m + k) D with hU
  have hUunit : IsUnit U := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, hU, coeff_mk, add_zero,
      ← IsLocalRing.residue_ne_zero_iff_isUnit]
    have := coeff_order hne
    rwa [hDb, coeff_map] at this
  have hdiv : ∀ k, ϖ ∣ coeff k (D - X ^ m * U) := by
    intro k
    rw [map_sub, coeff_X_pow_mul']
    split_ifs with hk
    · rw [hU, coeff_mk, Nat.add_sub_cancel' hk, sub_self]
      exact dvd_zero _
    · rw [sub_zero, ← Ideal.mem_span_singleton,
        ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        ← IsLocalRing.residue_eq_zero_iff, ← coeff_map]
      exact coeff_of_lt_order_toNat (φ := Db) k (by omega)
  obtain ⟨D', hD'⟩ := low_divide ϖ _ hdiv
  have hDeq : D = X ^ m * U + C ϖ * D' := by rw [← hD']; ring
  set I := Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)}
    with hI
  let q := Ideal.Quotient.mk I
  have hp : (q (C ϖ)) ^ n = 0 := by
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have h0 : (q X ^ m * ↑((hUunit.map q).unit) + q (C ϖ) * q D') * q g = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hDeq] at h
    simpa [map_mul, map_add, map_pow] using h
  have h3 := low_key _ _ _ _ _ m n hp h0
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h3
  have hmn : m * n ≤ n * m₀ := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left n hmm
  have := low_coeff_dvd (ϖ ^ n) (n * m₀) _ h3 (m * n) hmn
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at this
  exact hg (Ideal.mem_span_singleton.mpr this)
end Formalism.CyclotomicNorms
