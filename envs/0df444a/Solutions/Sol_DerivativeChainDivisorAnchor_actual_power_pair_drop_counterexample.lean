-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.actual_power_pair_drop_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:32:30.166393+00:00
-- url     : https://prove2.me/submissions/07b9422c-e09b-4cdf-9893-deb33e5b3517

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_PairDropNoGo
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
import Theorems.Thm_DerivativeChainDivisorAnchor_anchor_source_derivative
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
import Theorems.Thm_DerivativeChainDivisorAnchor_pair_ratio_bound
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





theorem childRadius_pow (k : ℕ) (hk : 3 ≤ k) :
    childRadius k ^ orbitCount k = (1+((k:ℝ)-1)*innerRadius k ^ orbitCount k)/(k:ℝ) := by
  unfold childRadius
  exact Real.rpow_inv_natCast_pow (childRadiusPower_bounds k hk).1.le (orbitCount_pos k hk).ne'







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
namespace DerivativeChainDivisorAnchor
noncomputable section





















theorem exists_coe_of_mem (s : Multiset ℂ) (x : ℂ) (hx : x ∈ s) : ∃ i : s, (i:ℂ)=x := by
  exact ⟨⟨x, ⟨0, Multiset.count_pos.mpr hx⟩⟩, rfl⟩





















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section





theorem power_source_monic (P : ℂ[X]) (hP : P.Monic) (r : ℕ) : (powerSource P r).Monic := hP.pow r



theorem power_source_degree (P : ℂ[X]) (r : ℕ) : (powerSource P r).natDegree = r*P.natDegree := by
  simp only [powerSource, natDegree_pow, mul_comm]



theorem power_source_roots (P : ℂ[X]) (r : ℕ) : (powerSource P r).roots = r • P.roots := by
  simp only [powerSource, roots_pow]



theorem power_derivative (P Q : ℂ[X]) (n r : ℕ) (hD : P.derivative = C (n:ℂ)*Q) :
    (powerSource P r).derivative = C (r*n:ℂ)*powerChild P Q r := by
  simp only [powerSource, powerChild, derivative_pow, hD, map_mul]
  ring



theorem power_root_mem (P : ℂ[X]) (r : ℕ) (i : (powerSource P r).roots) : (i:ℂ) ∈ P.roots := by
  have hi : (i:ℂ) ∈ r • P.roots := by simpa only [power_source_roots] using (Multiset.coe_mem (x := i))
  have hc := Multiset.count_pos.mpr hi
  by_contra h
  have hz := Multiset.count_eq_zero.mpr h
  simp [hz] at hc









end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section







theorem powerMultiplicity_pos (k : ℕ) (hk : 3 ≤ k) : 1 ≤ powerMultiplicity k := by
  have hq := orbitCount_pos k hk
  unfold powerMultiplicity
  omega

theorem pair_source_monic (k : ℕ) : (pairSource k).Monic :=
  power_source_monic _ (obstruction_source_monic k) _



theorem pair_degree_factor (k : ℕ) (hk : 3 ≤ k) :
    (pairSource k).natDegree = 12*(orbitCount k)^2*k := by
  rw [pairSource, power_source_degree, obstruction_degree k hk]
  unfold powerMultiplicity
  ring

theorem pair_degree (k : ℕ) (hk : 3 ≤ k) : (pairSource k).natDegree = 192*k^9 := by
  rw [pair_degree_factor k hk]
  unfold orbitCount
  ring

theorem pair_normalized_derivative (k : ℕ) (hk : 3 ≤ k) :
    C (((pairSource k).natDegree:ℂ)⁻¹)*(pairSource k).derivative = pairChild k := by
  have hD := power_derivative (obstructionSource k) (obstructionChild k) (orbitCount k*k)
    (powerMultiplicity k) (by simpa only [Nat.cast_mul] using obstruction_derivative k hk)
  have hN : (pairSource k).natDegree=powerMultiplicity k*(orbitCount k*k) := by
    rw [pairSource, power_source_degree, obstruction_degree k hk]
  change C (((pairSource k).natDegree:ℂ)⁻¹)*(powerSource (obstructionSource k) (powerMultiplicity k)).derivative = _
  rw [hD, hN, ← mul_assoc, ← map_mul]
  simp only [Nat.cast_mul]
  have hpos : 0 < powerMultiplicity k*(orbitCount k*k) := Nat.mul_pos (powerMultiplicity_pos k hk)
    (Nat.mul_pos (orbitCount_pos k hk) (by omega))
  have hn : (powerMultiplicity k*(orbitCount k*k):ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [inv_mul_cancel₀ hn, map_one, one_mul]
  rfl

theorem pair_roots_unit_disk (k : ℕ) (hk : 3 ≤ k) (i : (pairSource k).roots) : ‖(i:ℂ)‖ ≤ 1 := by
  obtain ⟨j, hj⟩ := exists_coe_of_mem (obstructionSource k).roots i (power_root_mem _ _ i)
  simpa only [hj] using obstruction_roots_unit_disk k hk j

theorem pair_centroid_zero (k : ℕ) (hk : 3 ≤ k) : (pairSource k).roots.sum = 0 := by
  simp only [pairSource, power_source_roots, Multiset.sum_nsmul, obstruction_centroid_zero k hk, nsmul_zero]









theorem pair_ratio_grows (k : ℕ) (hk : 3 ≤ k) : (k:ℝ)-1 < pairRatio k := by
  have h := (pair_ratio_bound k hk).2
  have hk0 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hs : (k:ℝ)-1 < (k:ℝ)^2/((k:ℝ)+1) := by
    apply (lt_div_iff₀ hk0).mpr
    nlinarith
  exact hs.trans h

theorem no_finite_pair_drop_factor (K : ℝ) : ∃ k : ℕ, 3 ≤ k ∧
    0 < pairDrop (pairSource k) (pairChild k) ∧
    K*pairDrop (pairSource k) (pairChild k) <
      (pairSource k).natDegree*(((pairSource k).natDegree:ℝ)-1)*uniformRootW1 (pairSource k) (pairChild k) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max (K+1) 2)
  have hk2 : (2:ℝ) < k := lt_of_le_of_lt (le_max_right (K+1) 2) hk
  have hk3 : 3 ≤ k := by exact_mod_cast hk2
  have hK : K < (k:ℝ)-1 := by have h:=lt_of_le_of_lt (le_max_left (K+1) 2) hk; linarith
  have hD := (pair_ratio_bound k hk3).1
  have hR := hK.trans (pair_ratio_grows k hk3)
  have h := (lt_div_iff₀ hD).mp hR
  refine ⟨k, hk3, hD, ?_⟩
  simpa only [pairRatio, poweredCost, mul_assoc] using h





end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor




































theorem solution (K : ℝ) : ∃ k : ℕ, 3 ≤ k ∧
    pairSource k=(obstructionSource k)^(12*orbitCount k) ∧ (pairSource k).Monic ∧
    (pairSource k).natDegree=192*k^9 ∧
    (∀ i : (pairSource k).roots, ‖(i:ℂ)‖ ≤ 1) ∧ (pairSource k).roots.sum=0 ∧
    C (((pairSource k).natDegree:ℂ)⁻¹)*(pairSource k).derivative=pairChild k ∧
    0 < pairDrop (pairSource k) (pairChild k) ∧
    K*pairDrop (pairSource k) (pairChild k) <
      (pairSource k).natDegree*(((pairSource k).natDegree:ℝ)-1)*uniformRootW1 (pairSource k) (pairChild k) := by
  obtain ⟨k, hk, hD, hK⟩ := no_finite_pair_drop_factor K
  exact ⟨k, hk, rfl, pair_source_monic k, pair_degree k hk, pair_roots_unit_disk k hk,
    pair_centroid_zero k hk, pair_normalized_derivative k hk, hD, hK⟩
