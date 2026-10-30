-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.actual_divisor_energy_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T21:22:45.588262+00:00
-- url     : https://prove2.me/submissions/652bd07e-ad12-4e95-9fbd-fc0d88f8a3cd

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
import Definitions.Def_DerivativeChainGini_PairDropSignedEnergy
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
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section














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



theorem multiset_sum_coe (s : Multiset ℂ) (f : ℂ → ℝ) :
    (s.map f).sum = ∑ i : s, f (i:ℂ) := by
  symm
  change ((Finset.univ : Finset s).val.map (fun i : s => f (i:ℂ))).sum = _
  rw [Multiset.map_univ]

theorem multisetPair_coe (s t : Multiset ℂ) :
    multisetPair s t = ∑ i : s, ∑ j : t, ‖(i:ℂ)-(j:ℂ)‖ := by
  unfold multisetPair
  simp_rw [multiset_sum_coe]

theorem multisetPair_symm (s t : Multiset ℂ) : multisetPair s t = multisetPair t s := by
  rw [multisetPair_coe, multisetPair_coe, Finset.sum_comm]
  simp_rw [norm_sub_rev]

theorem multisetPair_add_left (s t u : Multiset ℂ) :
    multisetPair (s+t) u = multisetPair s u+multisetPair t u := by
  simp only [multisetPair, Multiset.map_add, Multiset.sum_add]

theorem multisetPair_add_right (s t u : Multiset ℂ) :
    multisetPair s (t+u) = multisetPair s t+multisetPair s u := by
  simp only [multisetPair, Multiset.map_add, Multiset.sum_add, Multiset.sum_map_add]





theorem multisetPair_nonneg (s t : Multiset ℂ) : 0 ≤ multisetPair s t := by
  rw [multisetPair_coe]
  positivity

theorem multisetPair_disk_bound (s t : Multiset ℂ)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1) (ht : ∀ y ∈ t, ‖y‖ ≤ 1) :
    multisetPair s t ≤ 2*(s.card:ℝ)*(t.card:ℝ) := by
  rw [multisetPair_coe]
  have hterm (i : s) (j : t) : ‖(i:ℂ)-(j:ℂ)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [hs i (Multiset.coe_mem (x := i)), ht j (Multiset.coe_mem (x := j))])
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm i j))
  simp only [Finset.sum_const, Finset.card_univ, Multiset.card_coe, nsmul_eq_mul] at h
  nlinarith

theorem exists_coe_of_mem (s : Multiset ℂ) (x : ℂ) (hx : x ∈ s) : ∃ i : s, (i:ℂ)=x := by
  exact ⟨⟨x, ⟨0, Multiset.count_pos.mpr hx⟩⟩, rfl⟩





theorem positiveDivisor_card (n : ℕ) (a : ℝ) : (positiveDivisor n a).card = 2*(n+2) := by
  simp only [positiveDivisor, Multiset.card_add, Multiset.card_map]
  rw [← (IsAlgClosed.splits (base n)).natDegree_eq_card_roots, base_degree]
  omega

theorem negativeDivisor_card (n : ℕ) (b : ℝ) : (negativeDivisor n b).card = 2*(n+2)-1 := by
  simp only [negativeDivisor, Multiset.card_add, Multiset.card_map, Multiset.card_nsmul, Multiset.card_singleton, mul_one]
  rw [← (IsAlgClosed.splits (base n)).natDegree_eq_card_roots, base_degree]
  omega

theorem scaled_roots_disk (n : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ x ∈ (base n).roots.map (fun z => (r:ℂ)*z), ‖x‖ ≤ 1 := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  obtain ⟨i, rfl⟩ := exists_coe_of_mem (base n).roots z hz
  simpa [norm_mul, slot_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using hr1

theorem unit_roots_disk (n : ℕ) : ∀ x ∈ (base n).roots, ‖x‖ ≤ 1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := exists_coe_of_mem (base n).roots x hx
  exact le_of_eq (slot_norm n i)

theorem positiveDivisor_disk (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ x ∈ positiveDivisor n a, ‖x‖ ≤ 1 := by
  intro x hx
  rcases Multiset.mem_add.mp hx with h | h
  · exact scaled_roots_disk n a ha ha1 x h
  · exact unit_roots_disk n x h

theorem negativeDivisor_disk (n : ℕ) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ x ∈ negativeDivisor n b, ‖x‖ ≤ 1 := by
  intro x hx
  rcases Multiset.mem_add.mp hx with h | h
  · exact scaled_roots_disk n b hb hb1 x h
  · have hc := Multiset.count_pos.mpr h
    have hx : x=0 := by
      by_contra hx
      simp [Multiset.count_singleton, hx] at hc
    simp [hx]

theorem actual_divisor_cancellation (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    divisorEnergy (anchorSource n k a) (anchorChild n k b) =
      multisetPair (positiveDivisor n a) (negativeDivisor n b) -
      multisetPair (positiveDivisor n a) (positiveDivisor n a)/2 -
      multisetPair (negativeDivisor n b) (negativeDivisor n b)/2 := by
  let U := positiveDivisor n a
  let V := negativeDivisor n b
  let S := (k-2) • (base n).roots
  have hP : (anchorSource n k a).roots = U+S := by
    rw [anchor_source_roots n k a ha]
    dsimp [U, S, positiveDivisor]
    rw [show k-1=(k-2)+1 by omega, add_nsmul, one_nsmul]
    ac_rfl
  have hQ : (anchorChild n k b).roots = V+S := by
    rw [anchor_child_roots n k b hb]
    dsimp [V, S, negativeDivisor]
    ac_rfl
  change multisetPair (anchorSource n k a).roots (anchorChild n k b).roots -
      multisetPair (anchorSource n k a).roots (anchorSource n k a).roots/2 -
      multisetPair (anchorChild n k b).roots (anchorChild n k b).roots/2 = _
  rw [hP, hQ]
  simp only [multisetPair_add_left, multisetPair_add_right]
  rw [multisetPair_symm S U, multisetPair_symm S V]
  change _ = multisetPair U V-multisetPair U U/2-multisetPair V V/2
  ring



end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor










































theorem solution (n k : ℕ) (hk : 3 ≤ k) (a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    |divisorEnergy (anchorSource n k a) (anchorChild n k b)| < 8*(n+2:ℝ)^2 := by
  let U := positiveDivisor n a
  let V := negativeDivisor n b
  have hU := positiveDivisor_disk n a ha.le ha1
  have hV := negativeDivisor_disk n b hb.le hb1
  have hUV := multisetPair_disk_bound U V hU hV
  have hUU := multisetPair_disk_bound U U hU hU
  have hVV := multisetPair_disk_bound V V hV hV
  have hUV0 := multisetPair_nonneg U V
  have hUU0 := multisetPair_nonneg U U
  have hVV0 := multisetPair_nonneg V V
  have huc : (U.card:ℝ)=2*(n+2:ℝ) := by dsimp [U]; rw [positiveDivisor_card]; push_cast; ring
  have hvc : (V.card:ℝ)=2*(n+2:ℝ)-1 := by
    dsimp [V]
    rw [negativeDivisor_card, Nat.cast_sub (by omega : 1 ≤ 2*(n+2))]
    push_cast
    ring
  simp only [huc, hvc] at hUV hUU hVV
  rw [actual_divisor_cancellation n k hk a b ha.ne' hb.ne']
  change |multisetPair U V-multisetPair U U/2-multisetPair V V/2| < _
  rw [abs_lt]
  constructor <;> nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
