-- Prove2me | solution 1 for Formalism.ELL.ExponentialCoefficientWeight.inv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:03.2222+00:00
-- url     : https://prove2.me/submissions/d0dfff19-9e02-4e70-8577-1d54dcb5d44d

import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExpWeight
import Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_pow_le
import Theorems.Thm_Formalism_ELL_ExponentialCoefficientWeight_mul_le_strict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.ExponentialCoefficientWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.ExponentialCoefficientWeight
theorem _root_.solution {l E : PowerSeries K} {r : ℝ} (hr : 0 < r)
    (hE0 : constantCoeff E = 0) (hl1 : coeff 1 l = 1)
    (hl : ∀ m, 2 ≤ m → ‖coeff m l‖ ≤ r⁻¹ * r ^ m)
    (hsub : l.subst E = X) :
    ∀ n, 1 ≤ n → ‖coeff n E‖ ≤ r⁻¹ * r ^ n := by
  have hS : HasSubst E := HasSubst.of_constantCoeff_zero' hE0
  have hexp : ∀ n, coeff n (X : PowerSeries K) =
      ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (E ^ m) := by
    intro n
    rw [← hsub, coeff_subst' hS]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
    · simp only [smul_eq_mul]
    · intro m hm
      simp only [Function.mem_support] at hm
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hm
      rw [coeff_of_lt_order n, smul_zero]
      exact lt_of_lt_of_le (by exact_mod_cast (by omega : n < m))
        (le_order_pow_of_constantCoeff_eq_zero m hE0)
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have hEb : ∀ d < k + 1, ‖coeff d E‖ ≤ r⁻¹ * r ^ d := by
    intro d hd
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, coeff_zero_eq_constantCoeff_apply, hE0, norm_zero]; positivity
    · exact ih d hd h0
  have hEb' : ∀ d ≤ k, ‖coeff d E‖ ≤ r⁻¹ * r ^ d := fun d hd => hEb d (by omega)
  have hE : coeff (k + 1) E = coeff (k + 1) (X : PowerSeries K) -
      ∑ i ∈ Finset.range k, coeff (i + 2) l * coeff (k + 1) (E ^ (i + 2)) := by
    have h := hexp (k + 1)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    rw [h]
    simp only [zero_add, pow_one, pow_zero, hl1, one_mul, coeff_one, Nat.add_one_ne_zero,
      if_false, mul_zero, add_zero]
    ring
  rw [hE]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [coeff_X]
    split_ifs with h1
    · have : k = 0 := by omega
      subst this
      rw [norm_one, zero_add, pow_one, inv_mul_cancel₀ hr.ne']
    · rw [norm_zero]; positivity
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul]
    have hpow0 : constantCoeff (E ^ (i + 1)) = 0 := by
      rw [map_pow, hE0, zero_pow (Nat.succ_ne_zero _)]
    have hc : ‖coeff (k + 1) (E ^ (i + 2))‖ ≤ (r⁻¹ * r⁻¹ ^ (i + 1)) * r ^ (k + 1) := by
      rw [pow_succ' E (i + 1)]
      exact mul_le_strict hr.le hri.le (by positivity) hE0 hpow0 hEb
        (fun d hd => pow_le hr.le hri.le hEb' (i + 1) d (by omega))
    have ha := hl (i + 2) (by omega)
    have hone : r ^ (i + 2) * r⁻¹ ^ (i + 2) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow]
    calc ‖coeff (i + 2) l‖ * ‖coeff (k + 1) (E ^ (i + 2))‖
        ≤ (r⁻¹ * r ^ (i + 2)) * ((r⁻¹ * r⁻¹ ^ (i + 1)) * r ^ (k + 1)) :=
          mul_le_mul ha hc (norm_nonneg _) (by positivity)
      _ = r⁻¹ * r ^ (k + 1) * (r ^ (i + 2) * r⁻¹ ^ (i + 2)) := by ring
      _ = r⁻¹ * r ^ (k + 1) := by rw [hone, mul_one]
end Formalism.ELL.ExponentialCoefficientWeight
