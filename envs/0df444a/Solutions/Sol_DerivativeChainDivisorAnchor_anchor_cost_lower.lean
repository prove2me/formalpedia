-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.anchor_cost_lower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:45:58.189983+00:00
-- url     : https://prove2.me/submissions/43dbac41-6ad0-4a0d-903f-d7a55240281d

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Theorems.Thm_DerivativeChainDivisorAnchor_root_transport_zero_lower
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







theorem slot_root (n : ℕ) (i : Slots n) : (i : ℂ)^(n+2) = 1 := by
  have hi := (mem_roots (base_monic n).ne_zero).mp (Multiset.coe_mem (x := i))
  simpa [base, eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] using hi

theorem slot_norm (n : ℕ) (i : Slots n) : ‖(i : ℂ)‖ = 1 := by
  have hi := congrArg norm (slot_root n i)
  simp only [norm_pow, norm_one] at hi
  exact (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1) (by omega : n+2 ≠ 0)).mp (by simpa using hi)



















end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainContinuation
namespace DerivativeChainGiniFamily
noncomputable section










theorem slot_sum_map (n : ℕ) (f : ℂ → ℝ) :
    ∑ i : Slots n, f (rootSlot n i) = ((base n).roots.map f).sum := by
  change ((Finset.univ : Finset (Slots n)).val.map (fun i : Slots n => f (i : ℂ))).sum = _
  rw [Multiset.map_univ]













































end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section










theorem anchor_source_degree (n k : ℕ) (hk : 1 ≤ k) (a : ℝ) :
    (anchorSource n k a).natDegree = (n+2)*k := by
  rw [anchorSource, natDegree_mul ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero
    (pow_ne_zero _ (base_monic n).ne_zero), natDegree_scaleRoots, natDegree_pow, base_degree]
  calc
    _ = (n+2)*((k-1)+1) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hk]

theorem anchor_child_degree (n k : ℕ) (hk : 2 ≤ k) (b : ℝ) :
    (anchorChild n k b).natDegree = (n+2)*k-1 := by
  rw [anchorChild, natDegree_mul ((monic_X_pow _).mul ((base_monic n).pow _)).ne_zero
    ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero, natDegree_scaleRoots,
    natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (base_monic n).ne_zero),
    natDegree_X_pow, natDegree_pow, base_degree]
  have he : (n+1)+(k-2)*(n+2)+(n+2)+1 = (n+2)*k := by
    calc
      _ = (n+2)*((k-2)+2) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hk]
  omega



theorem anchor_child_roots (n k : ℕ) (b : ℝ) (hb : b ≠ 0) :
    (anchorChild n k b).roots = (n+1) • ({0} : Multiset ℂ) + (k-2) • (base n).roots +
      (base n).roots.map (fun z => (b:ℂ)*z) := by
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast hb
  rw [anchorChild, roots_mul (mul_ne_zero ((monic_X_pow _).mul ((base_monic n).pow _)).ne_zero
    ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero),
    roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (base_monic n).ne_zero)),
    roots_X_pow, roots_pow, roots_scaleRoots _ (isUnit_iff_ne_zero.mpr hbC)]



end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section
















theorem rootSum_child (n k : ℕ) (b : ℝ) (hb : b ≠ 0) (f : ℂ → ℝ) :
    rootSum (anchorChild n k b) f = (n+1 : ℝ)*f 0 +
      ((k-2:ℕ):ℝ)*orbitSum (rootSlot n) 1 f + orbitSum (rootSlot n) b f := by
  unfold rootSum
  rw [anchor_child_roots n k b hb]
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.sum_add,
    Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton, Multiset.sum_singleton,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [← slot_sum_map n (fun z => f ((b:ℂ)*z)), ← slot_sum_map n f]
  simp only [orbitSum, Complex.ofReal_one, one_mul]







end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section
attribute [local instance] Classical.propDecidable















theorem source_root_min_norm (n k : ℕ) (_hk : 3 ≤ k) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (i : (anchorSource n k a).roots) : a ≤ ‖(i:ℂ)‖ := by
  rcases source_root_norm_values n k a ha i with h | h
  · exact le_of_eq h.symm
  · simpa only [h] using ha1



theorem orbit_zero_indicator (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    orbitSum (rootSlot n) r (fun y => if y=0 then (1:ℝ) else 0) = 0 := by
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr
  have hz (i : Slots n) : (r:ℂ)*rootSlot n i ≠ 0 := by
    apply mul_ne_zero hrC
    have h := slot_norm n i
    intro he
    simp only [rootSlot] at he
    rw [he, norm_zero] at h
    norm_num at h
  simp [orbitSum, hz]

theorem child_zero_count (n k : ℕ) (b : ℝ) (hb : b ≠ 0) :
    rootSum (anchorChild n k b) (fun y => if y=0 then (1:ℝ) else 0) = n+1 := by
  rw [rootSum_child n k b hb]
  simp [orbit_zero_indicator n 1 one_ne_zero, orbit_zero_indicator n b hb]



end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor

attribute [local instance] Classical.propDecidable























theorem solution (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : b ≠ 0) :
    (n+1 : ℝ)*a ≤ (((anchorSource n k a).natDegree:ℝ)-1)*
      uniformRootW1 (anchorSource n k a) (anchorChild n k b) := by
  have hP : 0 < (anchorSource n k a).natDegree := by rw [anchor_source_degree n k (by omega)]; positivity
  have hlow : 6 ≤ (n+2)*k := Nat.mul_le_mul (by omega : 2 ≤ n+2) hk
  have hQ : 0 < (anchorChild n k b).natDegree := by rw [anchor_child_degree n k (by omega)]; omega
  have hw := root_transport_zero_lower (anchorSource n k a) (anchorChild n k b) hP hQ a ha.le
    (source_root_min_norm n k hk a ha ha1)
  rw [child_zero_count n k b hb] at hw
  have hQr : (0:ℝ) < (anchorChild n k b).natDegree := by exact_mod_cast hQ
  have hmul := mul_le_mul_of_nonneg_left hw hQr.le
  have he : (anchorChild n k b).natDegree * (a*((n+1:ℝ)/(anchorChild n k b).natDegree)) = (n+1:ℝ)*a := by
    field_simp
    <;> ring
  rw [he] at hmul
  rw [anchor_child_degree n k (by omega)] at hmul
  rw [anchor_source_degree n k (by omega)]
  have hdeg : 1 ≤ (n+2)*k := by omega
  rw [Nat.cast_sub hdeg] at hmul
  simpa using hmul
