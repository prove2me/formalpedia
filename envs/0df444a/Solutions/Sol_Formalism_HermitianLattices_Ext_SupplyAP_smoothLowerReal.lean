-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.smoothLowerReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:44.043534+00:00
-- url     : https://prove2.me/submissions/ee6e6578-4975-4110-8e23-05ef39038030

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_innerSum
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_regroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (c r : ℕ → ℝ) (hr : ∀ n, r n = ∑ d ∈ n.divisors, c d)
    (hc : ∀ d, |c d| ≤ 1) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ k, k ≠ 0 → 1 ≤ r (k ^ 2))
    (K N : ℕ) (x : ℝ) (hx : 0 < x) (hKx : (K : ℝ) ^ 2 ≤ x) (hKN : K ^ 2 ≤ N) :
    (K : ℝ) / Real.exp 1 ≤
      x * (∑ d ∈ Icc 1 N, c d / (d : ℝ)) + (∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)) +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by
  set E : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / x) with hE
  have hE0 : ∀ n, 0 < E n := fun n => Real.exp_pos _

  have hlow : (K : ℝ) / Real.exp 1 ≤ ∑ n ∈ Icc 1 N, r n * E n := by
    have hsub : (Icc 1 K).image (fun k => k ^ 2) ⊆ Icc 1 N := by
      intro n hn
      simp only [Finset.mem_image, Finset.mem_Icc] at hn ⊢
      obtain ⟨k, ⟨hk1, hkK⟩, rfl⟩ := hn
      exact ⟨Nat.one_le_pow _ _ hk1, le_trans (Nat.pow_le_pow_left hkK 2) hKN⟩
    calc (K : ℝ) / Real.exp 1 = ∑ _k ∈ Icc 1 K, (Real.exp 1)⁻¹ := by
          simp [div_eq_mul_inv]
      _ ≤ ∑ k ∈ Icc 1 K, r (k ^ 2) * E (k ^ 2) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hk' := Finset.mem_Icc.mp hk
          have h1 : 1 ≤ r (k ^ 2) := hr1 k (by omega)
          have h2 : (Real.exp 1)⁻¹ ≤ E (k ^ 2) := by
            rw [← Real.exp_neg, hE]
            apply Real.exp_le_exp.mpr
            have hkK : (k : ℝ) ≤ K := by exact_mod_cast hk'.2
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            have : ((k ^ 2 : ℕ) : ℝ) ≤ x := by
              push_cast
              exact le_trans (pow_le_pow_left₀ hk0 hkK 2) hKx
            rw [neg_div]
            exact neg_le_neg ((div_le_one hx).mpr this)
          calc (Real.exp 1)⁻¹ = 1 * (Real.exp 1)⁻¹ := by ring
            _ ≤ r (k ^ 2) * E (k ^ 2) := mul_le_mul h1 h2 (by positivity) (by linarith)
      _ = ∑ n ∈ (Icc 1 K).image (fun k => k ^ 2), r n * E n := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact Nat.pow_left_injective (n := 2) (by omega) hab
      _ ≤ ∑ n ∈ Icc 1 N, r n * E n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => mul_nonneg (hr0 n) (hE0 n).le)

  have hre : ∑ n ∈ Icc 1 N, r n * E n = ∑ d ∈ Icc 1 N, c d * ∑ m ∈ Icc 1 (N / d), E (d * m) := by
    have := regroup N (fun d n => c d * E n)
    simp only [← Finset.sum_mul, ← Finset.mul_sum] at this
    rw [← this]
    exact Finset.sum_congr rfl (fun n _ => by rw [hr n])
  have hup : ∑ d ∈ Icc 1 N, c d * ∑ m ∈ Icc 1 (N / d), E (d * m) ≤
      ∑ d ∈ Icc 1 N, (x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) +
        (x + 1) * Real.exp (-(N : ℝ) / x)) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    obtain ⟨T, hT0, hT1, hT⟩ := innerSum x hx d N (Finset.mem_Icc.mp hd).1
    rw [hE]
    simp only
    rw [hT]
    have h1 : -(c d * T) ≤ T := by
      have := abs_le.mp (hc d)
      nlinarith [this.1, this.2]
    have h2 : c d * (x / d + gExp ((d : ℝ) / x) - T) =
        x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) + -(c d * T) := by ring
    rw [h2]
    linarith
  have hfin : ∑ d ∈ Icc 1 N, (x * (c d / (d : ℝ)) + c d * gExp ((d : ℝ) / x) +
        (x + 1) * Real.exp (-(N : ℝ) / x)) =
      x * (∑ d ∈ Icc 1 N, c d / (d : ℝ)) + (∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)) +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  linarith
end Formalism.HermitianLattices.Ext.SupplyAP
