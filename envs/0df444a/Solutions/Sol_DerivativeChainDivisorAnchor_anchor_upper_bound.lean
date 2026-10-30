-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.anchor_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:11:07.86998+00:00
-- url     : https://prove2.me/submissions/f16b243c-20d1-4a90-bd92-2e28ba0a492f

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_DivisorAnchorFunctional
import Definitions.Def_DerivativeChainGini_DivisorOrbitEstimates
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_GiniCandidateB
import Theorems.Thm_DerivativeChainContinuation_finite_gini_disk_bound
import Theorems.Thm_DerivativeChainDivisorAnchor_orbitDistance_lipschitz
import Theorems.Thm_DerivativeChainDivisorAnchor_orbit_cross_quadratic
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

theorem base_roots_sum (n : ℕ) : (base n).roots.sum = 0 := by
  have h := (IsAlgClosed.splits (base n)).nextCoeff_eq_neg_sum_roots_of_monic (base_monic n)
  have hn : (base n).nextCoeff = 0 := by
    rw [nextCoeff, base_degree]
    simp [base, show n+2 ≠ 0 by omega,
      show n+2-1 = n+1 by omega, show n+1 ≠ n+2 by omega, show n+1 ≠ 0 by omega]
    simp only [coeff_one, show n+1 ≠ 0 by omega, if_false]
  rw [hn] at h
  exact neg_eq_zero.mp h.symm

theorem slots_sum (n : ℕ) : ∑ i : Slots n, (i : ℂ) = 0 := by
  rw [← Multiset.sum_eq_sum_coe]
  exact base_roots_sum n















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
open DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
noncomputable section
variable {ι : Type} [Fintype ι] [Nonempty ι]



theorem uniform_mass : (∑ i : ι, (1/(Fintype.card ι : ℝ))) = 1 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp





theorem orbitDistance_same (z : ι → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    orbitDistance z R R = R*orbitDistance z 1 1 := by
  unfold orbitDistance
  simp only [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR,
    Complex.ofReal_one, one_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring








theorem orbit_chord_bound (z : ι → ℂ) (hz : ∀ i, ‖z i‖=1)
    (hm : ∑ i, z i=0) : orbitDistance z 1 1 < 3/2 := by
  have hmean : (∑ i, ((1/(Fintype.card ι : ℝ):ℝ):ℂ)*z i) = 0 := by
    rw [← Finset.mul_sum, hm, mul_zero]
  have hg := finite_gini_disk_bound (fun _ : ι => (1/(Fintype.card ι : ℝ))) z
    (fun _ => by positivity) uniform_mass 0 0 1 (by norm_num) hmean
    (fun i => by simpa using le_of_eq (hz i))
  have hb : orbitDistance z 1 1 ≤ Real.sqrt 2 := by
    simpa [finiteGini, orbitDistance] using hg
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith



end
end DerivativeChainDivisorAnchor


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










theorem pairSum_distance {ι : Type} [Fintype ι] [Nonempty ι] (z : ι → ℂ) (R S : ℝ) :
    pairSum z R S = (Fintype.card ι : ℝ)^2*orbitDistance z R S := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold pairSum orbitDistance
  simp only [← Finset.mul_sum]
  field_simp
  <;> ring



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

theorem source_pair_decomposition (n k : ℕ) (a : ℝ) (ha : a ≠ 0) :
    rootPairSum (anchorSource n k a) (anchorSource n k a) =
      pairSum (rootSlot n) a a + ((k-1:ℕ):ℝ)*pairSum (rootSlot n) a 1 +
      ((k-1:ℕ):ℝ)*pairSum (rootSlot n) 1 a + ((k-1:ℕ):ℝ)^2*pairSum (rootSlot n) 1 1 := by
  unfold rootPairSum
  simp_rw [rootSum_source n k a ha]
  simp only [orbitSum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pairSum]
  ring

theorem cross_pair_decomposition (n k : ℕ) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha0 : 0 ≤ a) :
    rootPairSum (anchorSource n k a) (anchorChild n k b) =
      (n+1 : ℝ)*((n+2 : ℝ)*a) + ((k-2:ℕ):ℝ)*pairSum (rootSlot n) a 1 + pairSum (rootSlot n) a b +
      ((k-1:ℕ):ℝ)*((n+1 : ℝ)*(n+2 : ℝ) + ((k-2:ℕ):ℝ)*pairSum (rootSlot n) 1 1 + pairSum (rootSlot n) 1 b) := by
  unfold rootPairSum
  simp_rw [rootSum_source n k a ha, rootSum_child n k b hb]
  simp only [orbitSum, sub_zero, norm_mul, slot_norm, mul_one, rootSlot,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0, abs_one, Complex.ofReal_one, one_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, pairSum]
  simp only [Finset.sum_const, Finset.card_univ, slots_card, Nat.cast_add, Nat.cast_ofNat, nsmul_eq_mul]
  ring

theorem anchor_divisor_identity (n k : ℕ) (hk : 2 ≤ k) (a b : ℝ) (ha : a ≠ 0)
    (hb : b ≠ 0) (ha0 : 0 ≤ a) :
    rootAnchor (anchorSource n k a) (anchorChild n k b) =
      ((n+2 : ℝ)/(k:ℝ)) * (
        (orbitDistance (rootSlot n) a a-a) + ((k:ℝ)-1)*(orbitDistance (rootSlot n) 1 a-1) +
        (orbitDistance (rootSlot n) a 1-orbitDistance (rootSlot n) a b) +
        ((k:ℝ)-1)*(orbitDistance (rootSlot n) 1 1-orbitDistance (rootSlot n) 1 b)) +
      (a+(k:ℝ)-1)/(k:ℝ) := by
  unfold rootAnchor
  rw [source_pair_decomposition n k a ha, cross_pair_decomposition n k a b ha hb ha0,
    anchor_source_degree n k (by omega) a]
  simp_rw [pairSum_distance, slots_card]
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_sub hk]
  push_cast
  have hkn : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hqn : (n+2 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor




theorem solution (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    rootAnchor (anchorSource n k a) (anchorChild n k b) <
      (n+2 : ℝ)*(a/(2*(k:ℝ))+a^2/2+(1-b))+1 := by
  let z := rootSlot n
  have hz : ∀ i, ‖z i‖=1 := slot_norm n
  have hm : ∑ i, z i=0 := slots_sum n
  have hg := orbit_chord_bound z hz hm
  have hc := orbit_cross_quadratic z hz hm a
  have hd1 := orbitDistance_lipschitz z hz a b hb1
  have hd2 := orbitDistance_lipschitz z hz 1 b hb1
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkm : (0:ℝ) ≤ (k:ℝ)-1 := by
    have : (3:ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hga : orbitDistance z a a-a < a/2 := by
    rw [orbitDistance_same z a ha.le]
    nlinarith [mul_pos ha (sub_pos.mpr hg)]
  have hcross := mul_le_mul_of_nonneg_left hc hkm
  have hdiff := mul_le_mul_of_nonneg_left hd2 hkm
  have hbr : (orbitDistance z a a-a) + ((k:ℝ)-1)*(orbitDistance z 1 a-1) +
      (orbitDistance z a 1-orbitDistance z a b) +
      ((k:ℝ)-1)*(orbitDistance z 1 1-orbitDistance z 1 b) <
      a/2+((k:ℝ)-1)*a^2/2+(k:ℝ)*(1-b) := by linarith
  have hmul := mul_lt_mul_of_pos_left hbr (by positivity : (0:ℝ) < (n+2:ℝ)/(k:ℝ))
  have hscalar : (n+2:ℝ)/(k:ℝ)*(a/2+((k:ℝ)-1)*a^2/2+(k:ℝ)*(1-b)) +
      (a+(k:ℝ)-1)/(k:ℝ) ≤ (n+2:ℝ)*(a/(2*(k:ℝ))+a^2/2+(1-b))+1 := by
    have he : ((n+2:ℝ)*(a/(2*(k:ℝ))+a^2/2+(1-b))+1) -
        ((n+2:ℝ)/(k:ℝ)*(a/2+((k:ℝ)-1)*a^2/2+(k:ℝ)*(1-b))+(a+(k:ℝ)-1)/(k:ℝ)) =
        (n+2:ℝ)*a^2/(2*(k:ℝ))+(1-a)/(k:ℝ) := by field_simp; ring
    have hn : 0 ≤ (n+2:ℝ)*a^2/(2*(k:ℝ))+(1-a)/(k:ℝ) := by positivity
    linarith
  rw [anchor_divisor_identity n k (by omega) a b ha.ne' hb.ne' ha.le]
  change (n+2:ℝ)/(k:ℝ)*_+_ < _
  linarith
