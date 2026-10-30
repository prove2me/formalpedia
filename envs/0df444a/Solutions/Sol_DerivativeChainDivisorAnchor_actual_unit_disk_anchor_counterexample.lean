-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.actual_unit_disk_anchor_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:18:25.275974+00:00
-- url     : https://prove2.me/submissions/e33ea232-9121-4587-a236-3d6a31468b8e

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_cost_lower
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_lower_bound
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_source_derivative
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
import Theorems.Thm_DerivativeChainDivisorAnchor_obstruction_anchor_upper
import Theorems.Thm_DerivativeChainDivisorAnchor_source_root_norm_values
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace DerivativeChainGiniFamily
noncomputable section






theorem base_monic (n : ℕ) : (base n).Monic := by
  simpa [base] using monic_X_pow_sub_C (R := ℂ) 1 (n := n+2) (by omega)











theorem base_roots_sum (n : ℕ) : (base n).roots.sum = 0 := by
  have h := (IsAlgClosed.splits (base n)).nextCoeff_eq_neg_sum_roots_of_monic (base_monic n)
  have hn : (base n).nextCoeff = 0 := by
    rw [nextCoeff, base_degree]
    simp [base, show n+2 ≠ 0 by omega,
      show n+2-1 = n+1 by omega, show n+1 ≠ n+2 by omega, show n+1 ≠ 0 by omega]
    simp only [coeff_one, show n+1 ≠ 0 by omega, if_false]
  rw [hn] at h
  exact neg_eq_zero.mp h.symm

















end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section






theorem anchor_source_monic (n k : ℕ) (a : ℝ) : (anchorSource n k a).Monic := by
  exact ((monic_scaleRoots_iff _).mpr (base_monic n)).mul ((base_monic n).pow _)



theorem anchor_source_degree (n k : ℕ) (hk : 1 ≤ k) (a : ℝ) :
    (anchorSource n k a).natDegree = (n+2)*k := by
  rw [anchorSource, natDegree_mul ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero
    (pow_ne_zero _ (base_monic n).ne_zero), natDegree_scaleRoots, natDegree_pow, base_degree]
  calc
    _ = (n+2)*((k-1)+1) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hk]



theorem anchor_source_roots (n k : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (anchorSource n k a).roots = (base n).roots.map (fun z => (a:ℂ)*z) + (k-1) • (base n).roots := by
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  rw [anchorSource, roots_mul (mul_ne_zero ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero
    (pow_ne_zero _ (base_monic n).ne_zero)), roots_scaleRoots _ (isUnit_iff_ne_zero.mpr haC), roots_pow]





end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section
attribute [local instance] Classical.propDecidable

















theorem source_root_unit_disk (n k : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (i : (anchorSource n k a).roots) : ‖(i:ℂ)‖ ≤ 1 := by
  rcases source_root_norm_values n k a ha i with h | h
  · simpa only [h] using ha1
  · exact le_of_eq h







end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainDivisorAnchor
noncomputable section






theorem orbitCount_pos (k : ℕ) (hk : 3 ≤ k) : 0 < orbitCount k := by
  unfold orbitCount
  positivity

theorem orbit_index (k : ℕ) (hk : 3 ≤ k) : orbitCount k-2+2=orbitCount k := by
  have hp : 0 < k^4 := pow_pos (by omega : 0 < k) 4
  unfold orbitCount
  omega

theorem innerRadius_bounds (k : ℕ) (hk : 3 ≤ k) : 0 < innerRadius k ∧ innerRadius k < 1 := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hs : (0:ℝ) < (k:ℝ)^2 := by positivity
  unfold innerRadius
  constructor
  · positivity
  · apply (div_lt_one hs).mpr
    nlinarith



theorem childRadius_bounds (k : ℕ) (hk : 3 ≤ k) : 0 < childRadius k ∧ childRadius k < 1 := by
  have hp := childRadiusPower_bounds k hk
  unfold childRadius
  exact ⟨Real.rpow_pos_of_pos hp.1 _, Real.rpow_lt_one hp.1.le hp.2.1
    (inv_pos.mpr (by exact_mod_cast orbitCount_pos k hk))⟩

theorem childRadius_pow (k : ℕ) (hk : 3 ≤ k) :
    childRadius k ^ orbitCount k = (1+((k:ℝ)-1)*innerRadius k ^ orbitCount k)/(k:ℝ) := by
  unfold childRadius
  exact Real.rpow_inv_natCast_pow (childRadiusPower_bounds k hk).1.le (orbitCount_pos k hk).ne'





theorem parameter_cost_gap (k : ℕ) (hk : 3 ≤ k) :
    (k:ℝ)*(3*(k:ℝ)+2) < ((orbitCount k : ℝ)-1)*innerRadius k := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hs : (3:ℝ) ≤ (k:ℝ)^2-2*(k:ℝ) := by nlinarith [sq_nonneg ((k:ℝ)-3)]
  have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg (k:ℝ))
  have hgap : (0:ℝ) < (k:ℝ)^4-2*(k:ℝ)^3-1 := by nlinarith
  unfold orbitCount innerRadius
  push_cast
  rw [← mul_div_assoc, mul_one]
  apply (lt_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^2)).mpr
  nlinarith

end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section








theorem obstruction_source_monic (k : ℕ) : (obstructionSource k).Monic :=
  anchor_source_monic _ _ _

theorem obstruction_degree (k : ℕ) (hk : 3 ≤ k) :
    (obstructionSource k).natDegree = orbitCount k*k := by
  rw [obstructionSource, anchor_source_degree _ k (by omega), orbit_index k hk]

theorem obstruction_derivative (k : ℕ) (hk : 3 ≤ k) :
    (obstructionSource k).derivative = C (orbitCount k*k:ℂ)*obstructionChild k := by
  have h := anchor_source_derivative (orbitCount k-2) k (by omega : 2 ≤ k)
    (innerRadius k) (childRadius k) (by simpa only [orbit_index k hk] using childRadius_pow k hk)
  have hiC : ((orbitCount k-2:ℕ):ℂ)+2 = (orbitCount k:ℂ) := by exact_mod_cast orbit_index k hk
  simpa only [obstructionSource, obstructionChild, hiC] using h

theorem obstruction_normalized_derivative (k : ℕ) (hk : 3 ≤ k) :
    C ((orbitCount k*k:ℂ)⁻¹)*(obstructionSource k).derivative = obstructionChild k := by
  have hn : (orbitCount k*k:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (orbitCount_pos k hk).ne' (by omega : k ≠ 0))
  rw [obstruction_derivative k hk, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

theorem obstruction_anchor_lower (k : ℕ) (hk : 3 ≤ k) : (2/3:ℝ) ≤ obstructionAnchor k := by
  exact anchor_lower_bound (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (childRadius_bounds k hk).1 (childRadius_bounds k hk).2.le



theorem obstruction_cost_lower (k : ℕ) (hk : 3 ≤ k) :
    ((orbitCount k:ℝ)-1)*innerRadius k ≤ obstructionCost k := by
  have h := anchor_cost_lower (orbitCount k-2) k hk (innerRadius k) (childRadius k)
    (innerRadius_bounds k hk).1 (innerRadius_bounds k hk).2.le (childRadius_bounds k hk).1.ne'
  have hi : ((orbitCount k-2:ℕ):ℝ)+2 = (orbitCount k:ℝ) := by exact_mod_cast orbit_index k hk
  change _ ≤ (((anchorSource (orbitCount k-2) k (innerRadius k)).natDegree:ℝ)-1)*
    uniformRootW1 (anchorSource (orbitCount k-2) k (innerRadius k)) (anchorChild (orbitCount k-2) k (childRadius k))
  have hi1 : ((orbitCount k-2:ℕ):ℝ)+1 = (orbitCount k:ℝ)-1 := by linarith
  rw [hi1] at h
  exact h

theorem obstruction_ratio_unbounded (k : ℕ) (hk : 3 ≤ k) :
    (k:ℝ) < obstructionCost k/obstructionAnchor k := by
  have hA := obstruction_anchor_lower k hk
  have hAu := obstruction_anchor_upper k hk
  have hC := obstruction_cost_lower k hk
  have hgap := parameter_cost_gap k hk
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  apply (lt_div_iff₀ (by linarith : 0 < obstructionAnchor k)).mpr
  have hprod := mul_lt_mul_of_pos_left hAu hkR
  nlinarith

theorem no_finite_anchor_factor (K : ℝ) : ∃ k : ℕ, 3 ≤ k ∧
    0 < obstructionAnchor k ∧ K*obstructionAnchor k < obstructionCost k := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max K 2)
  have hk2 : (2:ℝ) < k := lt_of_le_of_lt (le_max_right K 2) hk
  have hk3 : 3 ≤ k := by exact_mod_cast hk2
  have hK : K < k := lt_of_le_of_lt (le_max_left K 2) hk
  have hA : 0 < obstructionAnchor k := by linarith [obstruction_anchor_lower k hk3]
  have hr := obstruction_ratio_unbounded k hk3
  have hc := (lt_div_iff₀ hA).mp (hK.trans hr)
  exact ⟨k, hk3, hA, hc⟩




theorem obstruction_roots_unit_disk (k : ℕ) (hk : 3 ≤ k)
    (i : (obstructionSource k).roots) : ‖(i:ℂ)‖ ≤ 1 := by
  exact source_root_unit_disk (orbitCount k-2) k (innerRadius k)
    (innerRadius_bounds k hk).1 (innerRadius_bounds k hk).2.le i

theorem obstruction_centroid_zero (k : ℕ) (hk : 3 ≤ k) : (obstructionSource k).roots.sum = 0 := by
  rw [obstructionSource, anchor_source_roots _ k _ (innerRadius_bounds k hk).1.ne']
  simp only [Multiset.sum_add, Multiset.sum_nsmul, base_roots_sum, nsmul_zero, add_zero]
  have h := Multiset.sum_map_mul_left (a := (innerRadius k:ℂ))
    (s := (base (orbitCount k-2)).roots) (f := fun z : ℂ => z)
  simpa only [Multiset.map_id', base_roots_sum, mul_zero] using h



end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor


































theorem solution (K : ℝ) : ∃ k : ℕ, 3 ≤ k ∧
    (obstructionSource k).Monic ∧ (obstructionSource k).natDegree = orbitCount k*k ∧
    (∀ i : (obstructionSource k).roots, ‖(i:ℂ)‖ ≤ 1) ∧
    (obstructionSource k).roots.sum = 0 ∧
    C ((orbitCount k*k:ℂ)⁻¹)*(obstructionSource k).derivative = obstructionChild k ∧
    0 < rootAnchor (obstructionSource k) (obstructionChild k) ∧
    K*rootAnchor (obstructionSource k) (obstructionChild k) <
      (((obstructionSource k).natDegree:ℝ)-1)*uniformRootW1 (obstructionSource k) (obstructionChild k) := by
  obtain ⟨k, hk, hA, hC⟩ := no_finite_anchor_factor K
  exact ⟨k, hk, obstruction_source_monic k, obstruction_degree k hk,
    obstruction_roots_unit_disk k hk, obstruction_centroid_zero k hk,
    obstruction_normalized_derivative k hk, hA, hC⟩
