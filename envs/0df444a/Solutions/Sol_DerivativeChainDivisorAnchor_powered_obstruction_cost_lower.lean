-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.powered_obstruction_cost_lower
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:27:22.149069+00:00
-- url     : https://prove2.me/submissions/9af0863d-f2d4-4f6d-94ea-5f1d9156f064

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorAnchorNoGo
import Definitions.Def_DerivativeChainGini_DivisorParameters
import Definitions.Def_DerivativeChainGini_DivisorRootTransport
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Definitions.Def_DerivativeChainGini_PairDropPolynomialPower
import Theorems.Thm_DerivativeChainDivisorAnchor_childRadiusPower_bounds
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






theorem anchor_source_monic (n k : ℕ) (a : ℝ) : (anchorSource n k a).Monic := by
  exact ((monic_scaleRoots_iff _).mpr (base_monic n)).mul ((base_monic n).pow _)

theorem anchor_child_monic (n k : ℕ) (b : ℝ) : (anchorChild n k b).Monic := by
  exact ((monic_X_pow _).mul ((base_monic n).pow _)).mul ((monic_scaleRoots_iff _).mpr (base_monic n))

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

theorem anchor_source_roots (n k : ℕ) (a : ℝ) (ha : a ≠ 0) :
    (anchorSource n k a).roots = (base n).roots.map (fun z => (a:ℂ)*z) + (k-1) • (base n).roots := by
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  rw [anchorSource, roots_mul (mul_ne_zero ((monic_scaleRoots_iff _).mpr (base_monic n)).ne_zero
    (pow_ne_zero _ (base_monic n).ne_zero)), roots_scaleRoots _ (isUnit_iff_ne_zero.mpr haC), roots_pow]

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














theorem rootSum_source (n k : ℕ) (a : ℝ) (ha : a ≠ 0) (f : ℂ → ℝ) :
    rootSum (anchorSource n k a) f = orbitSum (rootSlot n) a f +
      ((k-1:ℕ):ℝ)*orbitSum (rootSlot n) 1 f := by
  unfold rootSum
  rw [anchor_source_roots n k a ha]
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.sum_add,
    Multiset.map_nsmul, Multiset.sum_nsmul, nsmul_eq_mul]
  rw [← slot_sum_map n (fun z => f ((a:ℂ)*z)), ← slot_sum_map n f]
  simp only [orbitSum, Complex.ofReal_one, one_mul]

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









theorem power_source_degree (P : ℂ[X]) (r : ℕ) : (powerSource P r).natDegree = r*P.natDegree := by
  simp only [powerSource, natDegree_pow, mul_comm]

theorem power_child_degree (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (hn : 1 ≤ P.natDegree) (hdeg : Q.natDegree = P.natDegree-1) (r : ℕ) (hr : 1 ≤ r) :
    (powerChild P Q r).natDegree = r*P.natDegree-1 := by
  rw [powerChild, natDegree_mul (pow_ne_zero _ hP.ne_zero) hQ.ne_zero, natDegree_pow, hdeg]
  have he : (P.natDegree*(r-1)+(P.natDegree-1))+1 = r*P.natDegree := by
    calc
      _ = P.natDegree*(r-1)+P.natDegree := by omega
      _ = ((r-1)+1)*P.natDegree := by ring
      _ = _ := by rw [Nat.sub_add_cancel hr]
  rw [mul_comm P.natDegree (r-1)] at he
  omega

theorem power_source_roots (P : ℂ[X]) (r : ℕ) : (powerSource P r).roots = r • P.roots := by
  simp only [powerSource, roots_pow]

theorem power_child_roots (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (r : ℕ) :
    (powerChild P Q r).roots = (r-1) • P.roots+Q.roots := by
  rw [powerChild, roots_mul (mul_ne_zero (pow_ne_zero _ hP.ne_zero) hQ.ne_zero), roots_pow]





theorem power_root_mem (P : ℂ[X]) (r : ℕ) (i : (powerSource P r).roots) : (i:ℂ) ∈ P.roots := by
  have hi : (i:ℂ) ∈ r • P.roots := by simpa only [power_source_roots] using (Multiset.coe_mem (x := i))
  have hc := Multiset.count_pos.mpr hi
  by_contra h
  have hz := Multiset.count_eq_zero.mpr h
  simp [hz] at hc

theorem power_min_norm (P : ℂ[X]) (r : ℕ) (a : ℝ) (hmin : ∀ i : P.roots, a ≤ ‖(i:ℂ)‖)
    (i : (powerSource P r).roots) : a ≤ ‖(i:ℂ)‖ := by
  obtain ⟨j, hj⟩ := exists_coe_of_mem P.roots i (power_root_mem P r i)
  simpa only [hj] using hmin j

theorem power_child_zero_count (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (r : ℕ)
    (hzero : rootSum P (fun y => if y=0 then (1:ℝ) else 0)=0) :
    rootSum (powerChild P Q r) (fun y => if y=0 then (1:ℝ) else 0) =
      rootSum Q (fun y => if y=0 then (1:ℝ) else 0) := by
  unfold rootSum at *
  rw [power_child_roots P Q hP hQ r]
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul, hzero, nsmul_zero, zero_add]

theorem obstruction_zero_count (k : ℕ) (hk : 3 ≤ k) :
    rootSum (obstructionSource k) (fun y => if y=0 then (1:ℝ) else 0)=0 := by
  rw [obstructionSource, rootSum_source _ k _ (innerRadius_bounds k hk).1.ne']
  simp [orbit_zero_indicator _ 1 one_ne_zero, orbit_zero_indicator _ _ (innerRadius_bounds k hk).1.ne']



end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor






























theorem solution (k r : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r) :
    ((orbitCount k:ℝ)-1)*innerRadius k ≤
      (((powerSource (obstructionSource k) r).natDegree:ℝ)-1)*
        uniformRootW1 (powerSource (obstructionSource k) r) (powerChild (obstructionSource k) (obstructionChild k) r) := by
  let P := obstructionSource k
  let Q := obstructionChild k
  have hP : P.Monic := obstruction_source_monic k
  have hQ : Q.Monic := anchor_child_monic _ _ _
  have hn : 1 ≤ P.natDegree := by dsimp [P]; rw [obstruction_degree k hk]; exact Nat.mul_pos (orbitCount_pos k hk) (by omega)
  have hdeg : Q.natDegree = P.natDegree-1 := by
    dsimp [P, Q, obstructionSource, obstructionChild]
    rw [anchor_child_degree _ k (by omega), anchor_source_degree _ k (by omega)]
  have hS : 0 < (powerSource P r).natDegree := by rw [power_source_degree]; positivity
  have hbig : 2 ≤ r*P.natDegree := by
    have hqn : 2 ≤ orbitCount k := by have hi:=orbit_index k hk; omega
    have hd : 6 ≤ P.natDegree := by dsimp [P]; rw [obstruction_degree k hk]; exact Nat.mul_le_mul hqn hk
    have hh := Nat.mul_le_mul hr hd
    omega
  have hT : 0 < (powerChild P Q r).natDegree := by rw [power_child_degree P Q hP hQ hn hdeg r hr]; omega
  have hzero := power_child_zero_count P Q hP hQ r (obstruction_zero_count k hk)
  have hcz : rootSum (powerChild P Q r) (fun y => if y=0 then (1:ℝ) else 0) = (orbitCount k:ℝ)-1 := by
    rw [hzero]
    have h := child_zero_count (orbitCount k-2) k (childRadius k) (childRadius_bounds k hk).1.ne'
    have hi : ((orbitCount k-2:ℕ):ℝ)+2 = (orbitCount k:ℝ) := by exact_mod_cast orbit_index k hk
    change rootSum (anchorChild (orbitCount k-2) k (childRadius k)) _ = _
    rw [h]
    linarith
  have hm : ∀ i : P.roots, innerRadius k ≤ ‖(i:ℂ)‖ :=
    source_root_min_norm (orbitCount k-2) k hk (innerRadius k) (innerRadius_bounds k hk).1 (innerRadius_bounds k hk).2.le
  have hw := root_transport_zero_lower (powerSource P r) (powerChild P Q r) hS hT
    (innerRadius k) (innerRadius_bounds k hk).1.le (power_min_norm P r (innerRadius k) hm)
  rw [hcz] at hw
  have hTr : (0:ℝ) < (powerChild P Q r).natDegree := by exact_mod_cast hT
  have hmul := mul_le_mul_of_nonneg_left hw hTr.le
  have he : (powerChild P Q r).natDegree *
      (innerRadius k*(((orbitCount k:ℝ)-1)/(powerChild P Q r).natDegree)) =
      ((orbitCount k:ℝ)-1)*innerRadius k := by field_simp
  rw [he] at hmul
  have hd : (powerChild P Q r).natDegree=(powerSource P r).natDegree-1 := by
    rw [power_child_degree P Q hP hQ hn hdeg r hr, power_source_degree]
  rw [hd, Nat.cast_sub (by omega : 1 ≤ (powerSource P r).natDegree)] at hmul
  simpa only [P, Q, Nat.cast_one] using hmul
