-- Prove2me | solution 1 for GRH.centered_squarefree_separated_upper_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @meadowlark
-- created : 2026-11-21T02:37:01.969166+00:00
-- url     : https://prove2.me/submissions/8f1c2822-3f80-44e9-ae87-b85005a83379
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GRH_SquarefreeBilinear
import Theorems.Thm_GRH_moebius_harmonic_decay_of_bounded_dirichlet_prefixes
import Theorems.Thm_GRH_liouville_harmonic_le_of_moebius_harmonic_le
import Theorems.Thm_GRH_reduced_liouville_harmonic_le_of_modulus_one
import Theorems.Thm_GRH_mobius_character_and_progression_bounds_above_record
import Theorems.Thm_GRH_moebius_partial_sum_reduced_progression_power_bound_below_record

/- The exact separated upper-pairs estimate for the centered squarefree Liouville sum.
   The above-record branch uses four existing proved results. The full exponent range also
   uses the existing open below-record Möbius progression estimate.
   Sources: meadowlark's exact convolution and geometric decomposition, pragyan's centering,
   Yi's square-divisor transfer, and the harmonic estimates used by marozols. The squarefree
   sieve adapts raresbuhai's certificates. The public explanation gives submission links. -/

section
section
open Finset

namespace GRH

/-- Counting a single residue class on (0,M] differs from its interval length
divided by the modulus by strictly less than one. The class may be zero. -/
theorem residue_count_error_lt_one (q : ℕ) [NeZero q] (b : ZMod q) (M : ℕ) :
    |(((Ioc 0 M).filter (fun r : ℕ => (r : ZMod q) = b)).card : ℝ) -
      (M : ℝ) / (q : ℝ)| < 1 := by
  have hp : 0 < q := NeZero.pos q
  have hq : 0 < (q : ℚ) := by exact_mod_cast hp
  let x : ℚ := ((M : ℚ) - b.val) / q
  let y : ℚ := (0 - (b.val : ℚ)) / q
  have hyx : y ≤ x := by
    dsimp [x,y]
    apply div_le_div_of_nonneg_right _ hq.le
    linarith [Nat.cast_nonneg (α := ℚ) M]
  have subxy : x-y = (M : ℚ) / q := by dsimp [x,y]; ring
  let C := ((Ioc 0 M).filter (fun r : ℕ => (r : ZMod q) = b)).card
  have hpred (r : ℕ) : (r : ZMod q) = b ↔ r ≡ b.val [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  have hc : (C : ℤ) = ⌊x⌋ - ⌊y⌋ := by
    dsimp only [C]
    simp_rw [hpred]
    rw [Nat.Ioc_filter_modEq_card 0 M hp]
    exact max_eq_left (sub_nonneg.mpr (Int.floor_mono hyx))
  have hcq : (C : ℚ) = (⌊x⌋ : ℚ) - (⌊y⌋ : ℚ) := by exact_mod_cast hc
  have hlo : -1 < (C : ℚ) - (M : ℚ) / q := by
    rw [hcq, ← subxy]
    linarith [Int.lt_floor_add_one x, Int.floor_le y]
  have hhi : (C : ℚ) - (M : ℚ) / q < 1 := by
    rw [hcq, ← subxy]
    linarith [Int.floor_le x, Int.lt_floor_add_one y]
  apply abs_lt.mpr
  constructor
  · change -1 < (C : ℝ) - (M : ℝ) / q
    simpa using (Rat.cast_lt (K := ℝ)).mpr hlo
  · change (C : ℝ) - (M : ℝ) / q < 1
    simpa using (Rat.cast_lt (K := ℝ)).mpr hhi

theorem unit_mul_residue_count_error_le_one (q : ℕ) [NeZero q]
    (c a : ZMod q) (hc : IsUnit c) (M : ℕ) :
    |(((Ioc 0 M).filter (fun r : ℕ => c * (r : ZMod q) = a)).card : ℝ) -
      (M : ℝ) / (q : ℝ)| ≤ 1 := by
  let u := hc.unit
  have hue : (u : ZMod q) = c := hc.unit_spec
  have eqv (r : ℕ) : c * (r : ZMod q) = a ↔ (r : ZMod q) = ↑(u⁻¹) * a := by
    rw [← hue]
    constructor
    · intro h
      rw [← h, ← mul_assoc]
      simp
    · intro h
      rw [h, ← mul_assoc]
      simp
  simp_rw [eqv]
  exact (residue_count_error_lt_one q _ M).le

end GRH
end

section
open Finset

namespace GRH

/-- The initial interval can have a real endpoint. Integrality of the residue count
recovers the full unit error without paying an extra floor-rounding term. -/
theorem residue_count_real_cutoff_error_lt_one (q : ℕ) [NeZero q] (b : ZMod q) (M : ℕ)
    (X : ℝ) (hlo : (M : ℝ) ≤ X) (hhi : X < (M : ℝ) + 1) :
    |(((Ioc 0 M).filter (fun r : ℕ => (r : ZMod q) = b)).card : ℝ) -
      X / (q : ℝ)| < 1 := by
  let C := ((Ioc 0 M).filter (fun r : ℕ => (r : ZMod q) = b)).card
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hm := abs_lt.mp (residue_count_error_lt_one q b M)
  change -1 < (C : ℝ) - (M : ℝ)/q ∧ (C : ℝ) - (M : ℝ)/q < 1 at hm
  have hmlo : (M : ℝ) < ((C : ℝ)+1)*q := (div_lt_iff₀ hq).mp (by linarith [hm.1])
  have hmint : M < (C+1)*q := by exact_mod_cast hmlo
  have hs : (M : ℝ)+1 ≤ ((C : ℝ)+1)*q := by exact_mod_cast Nat.succ_le_of_lt hmint
  apply abs_lt.mpr
  constructor
  · change -1 < (C : ℝ) - X/q
    have hx : X/q < C+1 := (div_lt_iff₀ hq).mpr (hhi.trans_le hs)
    linarith
  · change (C : ℝ) - X/q < 1
    linarith [div_le_div_of_nonneg_right hlo hq.le, hm.2]

/-- Error at a rational cutoff formed by ordinary natural division. -/
theorem unit_mul_residue_count_div_error_le_one (q : ℕ) [NeZero q]
    (c a : ZMod q) (hc : IsUnit c) (J k : ℕ) (hk : 0 < k) :
    |(((Ioc 0 (J / k)).filter (fun r : ℕ => c * (r : ZMod q) = a)).card : ℝ) -
      (J : ℝ) / (k : ℝ) / (q : ℝ)| ≤ 1 := by
  let u := hc.unit
  have hue : (u : ZMod q) = c := hc.unit_spec
  have eqv (r : ℕ) : c * (r : ZMod q) = a ↔ (r : ZMod q) = ↑(u⁻¹) * a := by
    rw [← hue]
    constructor
    · intro h
      rw [← h, ← mul_assoc]
      simp
    · intro h
      rw [h, ← mul_assoc]
      simp
  simp_rw [eqv]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (residue_count_real_cutoff_error_lt_one q _ (J/k) _ ?_ ?_).le
  · apply (le_div_iff₀ hk').mpr
    exact_mod_cast Nat.div_mul_le_self J k
  · apply (div_lt_iff₀ hk').mpr
    rw [mul_comm]
    exact_mod_cast Nat.lt_mul_div_succ J hk

end GRH
end

section
/- The telescoping estimate and summability proofs adapt raresbuhai's verified
   Helfgott coprime squarefree-count certificate. Here the statements refer
   directly to the density series used in pragyan's squarefree progression model. -/

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace GRH

lemma shifted_reciprocal_square_sum_le (D K : ℕ) (hD : 1≤D) :
    (∑ n ∈ Finset.range K,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) := by
  have hpoint (n : ℕ) : 1/((n+D+1 : ℕ) : ℝ)^2 ≤
      1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ)<((n+D : ℕ) : ℝ) := by exact_mod_cast (show 0<n+D by omega)
    push_cast
    field_simp
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range K,(1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ)) := Finset.sum_le_sum (fun n hn => hpoint n)
    _ = 1/(D : ℝ)-1/((K+D : ℕ) : ℝ) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_assoc,add_comm,add_left_comm] using Finset.sum_range_sub' (fun n : ℕ => 1/((n+D : ℕ) : ℝ)) K
    _ ≤ _ := sub_le_self _ (by positivity)

lemma shifted_reciprocal_square_tsum_le (D : ℕ) (hD : 1≤D) :
    (∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => shifted_reciprocal_square_sum_le D K hD)

lemma coprime_moebius_reciprocal_square_norm_le (q n : ℕ) :
    ‖(if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)‖ ≤ 1/(n : ℝ)^2 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,Real.norm_eq_abs,abs_div]
    rw [show |(n : ℝ)^2| = (n : ℝ)^2 from abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n:=n)) (sq_nonneg _)
  · rw [if_neg hc,norm_zero]
    positivity

lemma coprime_moebius_reciprocal_square_summable (q : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) := by
  exact Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => coprime_moebius_reciprocal_square_norm_le q n)

lemma reciprocal_square_tsum_le_two : (∑' n : ℕ,1/(n : ℝ)^2) ≤ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at h
  have ht := shifted_reciprocal_square_tsum_le 1 (by norm_num)
  norm_num [add_assoc] at ht
  simp only [one_div]
  linarith

theorem centered_density_sum_le_two (q : ℕ) :
    |(∑' k : ℕ, if Nat.Coprime k q then (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)^2 else 0)| ≤ 2 := by
  have hf := coprime_moebius_reciprocal_square_summable q
  calc
    _ ≤ ∑' n : ℕ,‖if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ,1/(n : ℝ)^2 := hf.norm.tsum_le_tsum
      (fun n => coprime_moebius_reciprocal_square_norm_le q n) hasSum_zeta_two.summable
    _ ≤ _ := reciprocal_square_tsum_le_two

theorem centered_density_tail (q D : ℕ) (hD : 1≤D) :
    |(∑' k : ℕ, if Nat.Coprime k q then (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)^2 else 0)-
      (∑ n ∈ Finset.Ioc 0 D,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)| ≤ 1/(D : ℝ) := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hs : (∑ n ∈ Finset.range (D+1),f n) = ∑ n ∈ Finset.Ioc 0 D,f n := by
    rw [Finset.range_eq_Ico]
    have he : Finset.Ico 0 (D+1) = insert 0 (Finset.Ioc 0 D) := by ext n; simp
    rw [he,Finset.sum_insert (by simp)]
    simp [f]
  change |(∑' n : ℕ,f n)-(∑ n ∈ Finset.Ioc 0 D,f n)| ≤ _
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  have herr : (∑' n : ℕ,f n)-(∑ n ∈ Finset.Ioc 0 D,f n) = ∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [herr]
  have htail : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hnorm : Summable (fun n : ℕ => 1/((n+D+1 : ℕ) : ℝ)^2) :=
    hasSum_zeta_two.summable.comp_injective (fun n m h => by omega)
  calc
    _ ≤ ∑' n : ℕ,‖f (n+(D+1))‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2 :=
      htail.norm.tsum_le_tsum (fun n => by simpa [f,Nat.add_assoc] using coprime_moebius_reciprocal_square_norm_le q (n+(D+1))) hnorm
    _ ≤ _ := shifted_reciprocal_square_tsum_le D hD

end GRH
end
end

section
/- Square-divisor inversion and the floorRoot argument follow raresbuhai,
   Prove2Me submission 20d9eace-6b8f-4945-9af2-b863cdfe57df. -/
section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace GRH.SquarefreeSieve

lemma floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [floorRoot_two_eq_one_iff_squarefree n hn]


theorem cap {n M : ℕ} (hn : 0 < n) (hnM : n ≤ M) :
    (if Squarefree n then (1 : ℝ) else 0) =
      ∑ k ∈ Ioc 0 M.sqrt, if k^2 ∣ n then (moebius k : ℝ) else 0 := by
  have h : (if Squarefree n then (1 : ℤ) else 0) =
      ∑ k ∈ n.divisors, if k^2 ∣ n then moebius k else 0 := by
    rw [← moebius_square_divisor_expansion n hn.ne', moebius_sq]
  have he : n.divisors.filter (fun k => k^2 ∣ n) =
      (Ioc 0 M.sqrt).filter (fun k => k^2 ∣ n) := by
    ext k
    simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
    constructor
    · rintro ⟨⟨hk,_⟩,hs⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hk hn, Nat.le_sqrt.mpr
        (by simpa [pow_two] using (Nat.le_of_dvd hn hs).trans hnM)⟩,hs⟩
    · rintro ⟨_,hs⟩
      exact ⟨⟨dvd_trans (dvd_pow_self k (by decide : 2≠0)) hs,hn.ne'⟩,hs⟩
  simp only [← Finset.sum_filter] at h ⊢
  rw [← he]
  exact_mod_cast h

noncomputable def row (q : ℕ) (c a : ZMod q) (M : ℕ) : ℝ :=
  (((Ioc 0 M).filter fun j : ℕ => c * (j : ZMod q) = a).card : ℝ)

theorem div_class_card {q : ℕ} (c a : ZMod q) (M p : ℕ) (hp : 0 < p) :
    ((Ioc 0 M).filter (fun r : ℕ => p ∣ r ∧ c * (r : ZMod q) = a)).card =
      ((Ioc 0 (M / p)).filter fun j : ℕ => (c * (p : ZMod q)) * (j : ZMod q) = a).card := by
  symm
  apply Finset.card_bij (fun j _ => p*j)
  · intro j hj
    obtain ⟨hj,hr⟩ := mem_filter.mp hj
    obtain ⟨hj0,hjM⟩ := mem_Ioc.mp hj
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hp hj0,
      by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hjM⟩,
      dvd_mul_right p j, by simpa [Nat.cast_mul, mul_assoc] using hr⟩
  · intro i hi j hj h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro r hr
    obtain ⟨hr,⟨j,rfl⟩,hc⟩ := mem_filter.mp hr
    obtain ⟨h0,hM⟩ := mem_Ioc.mp hr
    have hj : 0 < j := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at h0
    exact ⟨j,mem_filter.mpr ⟨mem_Ioc.mpr ⟨hj, (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hM)⟩,
      by simpa [Nat.cast_mul, mul_assoc] using hc⟩,rfl⟩

theorem sieve {q : ℕ} (c a : ZMod q) (M : ℕ) :
    (((Ioc 0 M).filter (fun r : ℕ => Squarefree r ∧ c * (r : ZMod q) = a)).card : ℝ) =
      ∑ k ∈ Ioc 0 M.sqrt, (moebius k : ℝ) * row q (c * (k^2 : ℕ)) a (M / k^2) := by
  classical
  have point (r : ℕ) (hr : r ∈ Ioc 0 M) :
      (if Squarefree r ∧ c * (r : ZMod q) = a then (1:ℝ) else 0) =
      ∑ k ∈ Ioc 0 M.sqrt, if k^2 ∣ r ∧ c * (r : ZMod q) = a then (moebius k : ℝ) else 0 := by
    by_cases hc : c * (r : ZMod q) = a
    · simpa only [hc, and_true] using cap (mem_Ioc.mp hr).1 (mem_Ioc.mp hr).2
    · simp [hc]
  calc
    _ = ∑ r ∈ Ioc 0 M, if Squarefree r ∧ c * (r : ZMod q) = a then (1:ℝ) else 0 := by simp
    _ = _ := Finset.sum_congr rfl point
    _ = ∑ k ∈ Ioc 0 M.sqrt, ∑ r ∈ Ioc 0 M, if k^2 ∣ r ∧ c * (r : ZMod q) = a then (moebius k : ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_class_card c a M (k^2) (pow_pos (mem_Ioc.mp hk).1 2)]
      unfold row
      ring

end GRH.SquarefreeSieve
end
end

section
namespace GRH
namespace SquarefreeSieve
open Finset ArithmeticFunction
open scoped Classical

private theorem no_class {q : ℕ} {c a : ZMod q} (hc : ¬ IsUnit c) (ha : IsUnit a)
    (r : ℕ) : c * (r : ZMod q) ≠ a := by
  intro h
  exact hc (isUnit_of_mul_isUnit_left (h ▸ ha : IsUnit (c * (r : ZMod q))))

private theorem row_zero {q : ℕ} {c a : ZMod q} (hc : ¬ IsUnit c) (ha : IsUnit a) (M : ℕ) :
    row q c a M = 0 := by simp [row, no_class hc ha]

theorem finite_error {q : ℕ} [NeZero q] (c a : ZMod q) (hc : IsUnit c) (ha : IsUnit a)
    (N b : ℕ) (hb : 0 < b) :
    |(((Ioc 0 (N/b)).filter (fun r : ℕ => Squarefree r ∧ c * (r : ZMod q) = a)).card : ℝ) -
      ((N:ℝ)/(b:ℝ)/(q:ℝ)) *
        ∑ k ∈ Ioc 0 (N/b).sqrt, (if Nat.Coprime k q then (moebius k : ℝ)/(k:ℝ)^2 else 0)| ≤
      ((N/b).sqrt : ℝ) := by
  rw [sieve, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _k ∈ Ioc 0 (N/b).sqrt, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk0 : 0 < k := (mem_Ioc.mp hk).1
          by_cases hcop : Nat.Coprime k q
          · rw [if_pos hcop]
            have hu : IsUnit (c * ((k^2 : ℕ) : ZMod q)) := by
              rw [Nat.cast_pow]
              exact hc.mul (((ZMod.isUnit_iff_coprime _ _).mpr hcop).pow 2)
            have hr := GRH.unit_mul_residue_count_div_error_le_one q _ a hu N (b*k^2)
              (Nat.mul_pos hb (pow_pos hk0 2))
            change |row q _ a (N/(b*k^2)) - (N:ℝ)/((b*k^2:ℕ):ℝ)/(q:ℝ)| ≤ 1 at hr
            rw [Nat.div_div_eq_div_mul]
            have eqn (z : ℝ) : (moebius k : ℝ)*z - ((N:ℝ)/b/q)*((moebius k : ℝ)/(k:ℝ)^2) =
                (moebius k : ℝ)*(z - (N:ℝ)/((b*k^2:ℕ):ℝ)/(q:ℝ)) := by
              push_cast
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
            rw [eqn, abs_mul]
            have hm : |(moebius k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n:=k)
            exact (mul_le_mul hm hr (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
          · have hu : ¬ IsUnit (c * ((k^2:ℕ):ZMod q)) := by
              intro hu
              apply hcop
              apply (ZMod.isUnit_iff_coprime k q).mp
              have hsq := isUnit_of_mul_isUnit_right hu
              rw [Nat.cast_pow, pow_two] at hsq
              exact isUnit_of_mul_isUnit_left hsq
            rw [row_zero hu ha, if_neg hcop]
            norm_num
       _ = _ := by simp

theorem count_error {q : ℕ} [NeZero q] (c a : ZMod q) (hc : IsUnit c) (ha : IsUnit a)
    (N b : ℕ) (hb : 0 < b) (hNb : b ≤ N) :
    |(((Ioc 0 (N/b)).filter (fun r : ℕ => Squarefree r ∧ c * (r : ZMod q) = a)).card : ℝ) -
      squarefreeProgressionDensity q * (N:ℝ)/(b:ℝ)| ≤ 5 * Real.sqrt ((N:ℝ)/(b:ℝ)) := by
  let M := N/b
  let T := M.sqrt
  let X := (N:ℝ)/(b:ℝ)
  let f := fun k : ℕ => if Nat.Coprime k q then (moebius k : ℝ)/(k:ℝ)^2 else 0
  let C : ℝ := (((Ioc 0 M).filter (fun r : ℕ => Squarefree r ∧ c * (r : ZMod q) = a)).card : ℝ)
  have hT : 1 ≤ T := Nat.le_sqrt.mpr (by simpa [M] using (Nat.le_div_iff_mul_le hb).mpr (by simpa using hNb) : 1*1 ≤ M)
  have hT' : (1:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT
  have hpos : 0 < (T:ℝ) := by linarith
  have hq : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (NeZero.pos q)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hTm : (T:ℝ)^2 ≤ (M:ℝ) := by exact_mod_cast Nat.sqrt_le' M
  have hTx : (T:ℝ) ≤ Real.sqrt X := Real.le_sqrt_of_sq_le (hTm.trans (Nat.cast_div_le))
  have hM : X < (M:ℝ)+1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hb : 0 < (b:ℝ))).mpr
    exact_mod_cast (by simpa [M,Nat.mul_comm] using Nat.lt_mul_div_succ N hb : N < (M+1)*b)
  have hTup : (M:ℝ)+1 ≤ ((T:ℝ)+1)^2 := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_succ_sqrt' M))
  have hXT : X ≤ 4*(T:ℝ)^2 := by
    have hprod := mul_nonneg (by linarith : (0:ℝ) ≤ T-1) (by linarith : (0:ℝ) ≤ 3*(T:ℝ)+1)
    nlinarith [hM.le.trans hTup]
  have ht := GRH.centered_density_tail q T hT
  change |(∑' k, f k)-(∑ k ∈ Ioc 0 T, f k)| ≤ 1/(T:ℝ) at ht
  have hfin := finite_error c a hc ha N b hb
  change |C-(X/q)*(∑ k ∈ Ioc 0 T, f k)| ≤ (T:ℝ) at hfin
  have hcq : 0 ≤ X/(q:ℝ) := by positivity
  have htail : |(X/q)*(∑ k ∈ Ioc 0 T, f k) - (X/q)*(∑' k, f k)| ≤ 4*(T:ℝ) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hcq, abs_sub_comm]
    calc _ ≤ (X/q)*(1/(T:ℝ)) := mul_le_mul_of_nonneg_left ht hcq
         _ ≤ X*(1/(T:ℝ)) := mul_le_mul_of_nonneg_right (div_le_self hX hq) (by positivity)
         _ ≤ 4*(T:ℝ) := by
           rw [one_div, ← div_eq_mul_inv]
           apply (div_le_iff₀ hpos).mpr
           nlinarith [hXT]
  have hfinal : |C-(X/q)*(∑' k, f k)| ≤ 5*Real.sqrt X := by
    calc _ ≤ |C-(X/q)*(∑ k ∈ Ioc 0 T, f k)| + |(X/q)*(∑ k ∈ Ioc 0 T, f k)-(X/q)*(∑' k, f k)| := abs_sub_le _ _ _
         _ ≤ (T:ℝ) + 4*(T:ℝ) := add_le_add hfin htail
         _ ≤ _ := by linarith
  have hdens : squarefreeProgressionDensity q * (N:ℝ)/(b:ℝ) = (X/q)*(∑' k, f k) := by
    dsimp only [squarefreeProgressionDensity,X,f]
    ring
  rw [hdens]
  exact hfinal

end SquarefreeSieve

theorem squarefreeProgressionCount_error (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (N d e : ℕ) (hd : 0 < d) (he : 0 < e) (hde : d*e ≤ N) :
    |squarefreeProgressionCount q a N d e -
      (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        squarefreeProgressionDensity q * (N:ℝ) / ((d:ℝ)*(e:ℝ)) else 0)| ≤
      5 * Real.sqrt ((N:ℝ)/((d:ℝ)*(e:ℝ))) := by
  by_cases hu : IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q)
  · have hc : IsUnit ((d*e:ℕ) : ZMod q) := by simpa only [Nat.cast_mul] using hu.1.mul hu.2
    rw [if_pos hu]
    simpa only [squarefreeProgressionCount,Nat.cast_mul] using
      SquarefreeSieve.count_error (((d*e:ℕ) : ZMod q)) a hc ha N (d*e) (Nat.mul_pos hd he) hde
  · have hno (r : ℕ) : ((d*e*r:ℕ):ZMod q) ≠ a := by
      intro h; apply hu
      rw [← h, Nat.cast_mul, Nat.cast_mul] at ha
      exact IsUnit.mul_iff.mp (isUnit_of_mul_isUnit_left ha)
    simp only [Nat.cast_mul] at hno
    simp [squarefreeProgressionCount, hno, hu] <;> positivity

end GRH
end
end

section
open scoped BigOperators
open Finset

namespace CenteredMatching

/-- The reciprocal geometric mean is at most the arithmetic mean of the two reciprocals. -/
lemma inv_sqrt_mul_le_mean (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (Real.sqrt (x * y))⁻¹ ≤ x⁻¹ + y⁻¹ := by
  have hx' : ((Real.sqrt x)⁻¹) ^ 2 = x⁻¹ := by rw [inv_pow, Real.sq_sqrt hx]
  have hy' : ((Real.sqrt y)⁻¹) ^ 2 = y⁻¹ := by rw [inv_pow, Real.sq_sqrt hy]
  rw [Real.sqrt_mul hx, mul_inv_rev]
  nlinarith [sq_nonneg ((Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹)]

/-- Group one reciprocal coordinate by its fibers. -/
lemma sum_inv_coordinate {S : Finset (ℕ × ℕ)} {U Δ : ℕ} (g : ℕ × ℕ → ℕ)
    (hg : ∀ p ∈ S, g p ∈ Ioc 0 U)
    (hdegree : ∀ k ∈ Ioc 0 U, (S.filter (fun p ↦ g p = k)).card ≤ Δ) :
    ∑ p ∈ S, ((g p : ℕ) : ℝ)⁻¹ ≤ (Δ : ℝ) * (1 + Real.log U) := by
  have hI : Ioc 0 U = Icc 1 U := by ext k; simp [Nat.succ_le_iff]
  have hH : ∑ k ∈ Ioc 0 U, (k : ℝ)⁻¹ ≤ 1 + Real.log U := by
    simpa [hI, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv] using harmonic_le_one_add_log U
  calc
    ∑ p ∈ S, ((g p : ℕ) : ℝ)⁻¹ =
        ∑ k ∈ Ioc 0 U, ∑ p ∈ S.filter (fun p ↦ g p = k), ((g p : ℕ) : ℝ)⁻¹ :=
      (sum_fiberwise_of_maps_to hg _).symm
    _ ≤ ∑ k ∈ Ioc 0 U, (Δ : ℝ) * (k : ℝ)⁻¹ := by
      refine sum_le_sum fun k hk ↦ ?_
      calc
        _ = ∑ _p ∈ S.filter (fun p ↦ g p = k), (k : ℝ)⁻¹ := by
          refine sum_congr rfl fun p hp ↦ ?_
          rw [(mem_filter.mp hp).2]
        _ = _ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hdegree k hk)) (by positivity)
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hH (by positivity)

/-- Summing the two fiber bounds controls all inverse square-root pair weights. -/
theorem sum_inv_sqrt_le {S : Finset (ℕ × ℕ)} {U Δ : ℕ}
    (hbox : S ⊆ (Ioc 0 U) ×ˢ (Ioc 0 U))
    (hrow : ∀ k ∈ Ioc 0 U, (S.filter (fun p ↦ p.1 = k)).card ≤ Δ)
    (hcol : ∀ k ∈ Ioc 0 U, (S.filter (fun p ↦ p.2 = k)).card ≤ Δ) :
    ∑ p ∈ S, (Real.sqrt ((p.1 : ℝ) * p.2))⁻¹ ≤ (Δ : ℝ) * (1 + Real.log U) := by
  have hr := sum_inv_coordinate Prod.fst (fun p hp ↦ (mem_product.mp (hbox hp)).1) hrow
  have hc := sum_inv_coordinate Prod.snd (fun p hp ↦ (mem_product.mp (hbox hp)).2) hcol
  have h := sum_le_sum (s := S) (fun p _ ↦
    inv_sqrt_mul_le_mean (p.1 : ℝ) (p.2 : ℝ) (by positivity) (by positivity))
  rw [← mul_sum, sum_add_distrib] at h
  linarith

/-- A pointwise envelope of size K / √(de) on a bounded-degree set gives a logarithmic loss. -/
theorem abs_sum_le {S : Finset (ℕ × ℕ)} {U Δ : ℕ} {K : ℝ} (F : ℕ × ℕ → ℝ)
    (hbox : S ⊆ (Ioc 0 U) ×ˢ (Ioc 0 U))
    (hrow : ∀ k ∈ Ioc 0 U, (S.filter (fun p ↦ p.1 = k)).card ≤ Δ)
    (hcol : ∀ k ∈ Ioc 0 U, (S.filter (fun p ↦ p.2 = k)).card ≤ Δ)
    (hK : 0 ≤ K) (hF : ∀ p ∈ S, |F p| ≤ K / Real.sqrt ((p.1 : ℝ) * p.2)) :
    |∑ p ∈ S, F p| ≤ K * (Δ : ℝ) * (1 + Real.log U) := by
  calc
    _ ≤ ∑ p ∈ S, |F p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, K * (Real.sqrt ((p.1 : ℝ) * p.2))⁻¹ := by
      simpa only [div_eq_mul_inv] using sum_le_sum hF
    _ ≤ _ := by
      rw [← mul_sum, mul_assoc]
      exact mul_le_mul_of_nonneg_left (sum_inv_sqrt_le hbox hrow hcol) hK

end CenteredMatching
end

section
open scoped BigOperators
open Finset

namespace CenteredMatching

/-- Absorb the harmonic loss when the degree may grow like (N+1)^α. -/
theorem sqrt_mul_rpow_log_le (N : ℕ) {α σ : ℝ} (hgap : 1 / 2 + α < σ) :
    Real.sqrt (N : ℝ) * ((N : ℝ) + 1) ^ α * (1 + Real.log (N.sqrt : ℝ)) ≤
      (1 + (σ - (1 / 2 + α))⁻¹) * ((N : ℝ) + 1) ^ σ := by
  let x : ℝ := N + 1
  let ε := σ - (1 / 2 + α)
  have hε : 0 < ε := sub_pos.mpr hgap
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hx' : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hN : (N : ℝ) ≤ x := by dsimp [x]; linarith
  have hU : (N.sqrt : ℝ) ≤ x := (Nat.cast_le.mpr (Nat.sqrt_le_self N)).trans hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ x ^ (1/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (by positivity) hN (by norm_num)
  have hlog : 1 + Real.log (N.sqrt : ℝ) ≤ (1 + ε⁻¹) * x ^ ε := by
    have hpow := Real.rpow_le_rpow (show 0 ≤ (N.sqrt : ℝ) by positivity) hU hε.le
    have h := (Real.log_natCast_le_rpow_div N.sqrt hε).trans
      (div_le_div_of_nonneg_right hpow hε.le)
    rw [div_eq_mul_inv] at h
    nlinarith [Real.one_le_rpow hx hε.le]
  change Real.sqrt (N : ℝ) * x ^ α * (1 + Real.log (N.sqrt : ℝ)) ≤ (1 + ε⁻¹) * x ^ σ
  calc
    _ ≤ x ^ (1/2 : ℝ) * x ^ α * ((1 + ε⁻¹) * x ^ ε) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hx'.le _)) hlog
        (by linarith [Real.log_natCast_nonneg N.sqrt]) (by positivity)
    _ = (1 + ε⁻¹) * x ^ (1/2 + α + ε) := by rw [Real.rpow_add hx', Real.rpow_add hx']; ring
    _ = _ := by congr 2; dsimp [ε]; ring

/-- Uniform sparse removal for any degree bounded by a power strictly below the gap. -/
theorem abs_sum_le_rpow {S : Finset (ℕ × ℕ)} {N Δ : ℕ} {K α σ : ℝ} (F : ℕ × ℕ → ℝ)
    (hgap : 1 / 2 + α < σ) (hK : 0 ≤ K)
    (hbox : S ⊆ (Ioc 0 N.sqrt) ×ˢ (Ioc 0 N.sqrt))
    (hrow : ∀ k ∈ Ioc 0 N.sqrt, (S.filter (fun p ↦ p.1 = k)).card ≤ Δ)
    (hcol : ∀ k ∈ Ioc 0 N.sqrt, (S.filter (fun p ↦ p.2 = k)).card ≤ Δ)
    (hΔ : (Δ : ℝ) ≤ ((N : ℝ) + 1) ^ α)
    (hF : ∀ p ∈ S, |F p| ≤ (K * Real.sqrt (N : ℝ)) / Real.sqrt ((p.1 : ℝ) * p.2)) :
    |∑ p ∈ S, F p| ≤ (K * (1 + (σ - (1 / 2 + α))⁻¹)) * ((N : ℝ) + 1) ^ σ := by
  have h := abs_sum_le F hbox hrow hcol (mul_nonneg hK (Real.sqrt_nonneg _)) hF
  calc
    _ ≤ K * Real.sqrt (N : ℝ) * (Δ : ℝ) * (1 + Real.log (N.sqrt : ℝ)) := h
    _ ≤ K * (Real.sqrt (N : ℝ) * ((N : ℝ) + 1) ^ α * (1 + Real.log (N.sqrt : ℝ))) := by
      rw [← mul_assoc, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ (by positivity))
        (by linarith [Real.log_natCast_nonneg N.sqrt])
    _ ≤ _ := by
      rw [mul_assoc K]
      exact mul_le_mul_of_nonneg_left (sqrt_mul_rpow_log_le N hgap) hK

/-- The degree bound may include a fixed coefficient L; taking α = 0 covers all fixed degrees. -/
theorem abs_sum_le_rpow_scaled {S : Finset (ℕ × ℕ)} {N Δ : ℕ} {K L α σ : ℝ}
    (F : ℕ × ℕ → ℝ) (hgap : 1 / 2 + α < σ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hbox : S ⊆ (Ioc 0 N.sqrt) ×ˢ (Ioc 0 N.sqrt))
    (hrow : ∀ k ∈ Ioc 0 N.sqrt, (S.filter (fun p ↦ p.1 = k)).card ≤ Δ)
    (hcol : ∀ k ∈ Ioc 0 N.sqrt, (S.filter (fun p ↦ p.2 = k)).card ≤ Δ)
    (hΔ : (Δ : ℝ) ≤ L * ((N : ℝ) + 1) ^ α)
    (hF : ∀ p ∈ S, |F p| ≤ (K * Real.sqrt (N : ℝ)) / Real.sqrt ((p.1 : ℝ) * p.2)) :
    |∑ p ∈ S, F p| ≤ (K * L * (1 + (σ - (1 / 2 + α))⁻¹)) * ((N : ℝ) + 1) ^ σ := by
  have h := abs_sum_le F hbox hrow hcol (mul_nonneg hK (Real.sqrt_nonneg _)) hF
  calc
    _ ≤ K * Real.sqrt (N : ℝ) * (Δ : ℝ) * (1 + Real.log (N.sqrt : ℝ)) := h
    _ ≤ K * Real.sqrt (N : ℝ) * (L * ((N : ℝ) + 1) ^ α) * (1 + Real.log (N.sqrt : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ (by positivity))
        (by linarith [Real.log_natCast_nonneg N.sqrt])
    _ = (K * L) * (Real.sqrt (N : ℝ) * ((N : ℝ) + 1) ^ α * (1 + Real.log (N.sqrt : ℝ))) := by ring
    _ ≤ _ := by
      rw [mul_assoc (K * L)]
      exact mul_le_mul_of_nonneg_left (sqrt_mul_rpow_log_le N hgap) (mul_nonneg hK hL)

end CenteredMatching
end

section
open Finset
open scoped Classical BigOperators

namespace MeadowlarkSquarefree

noncomputable def term (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  (ArithmeticFunction.liouville p.1 : ℝ) * (ArithmeticFunction.liouville p.2 : ℝ) *
  (GRH.squarefreeProgressionCount q a N p.1 p.2 -
    if IsUnit (p.1 : ZMod q) ∧ IsUnit (p.2 : ZMod q) then
      GRH.squarefreeProgressionDensity q * (N : ℝ) / ((p.1 : ℝ) * p.2) else 0)

abbrev box (U : ℕ) := (Ioc 0 U) ×ˢ (Ioc 0 U)

theorem sum_box (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    GRH.centeredSquarefreeBilinear q a N = ∑ p ∈ box N.sqrt, term q a N p := by
  classical
  rw [Finset.sum_product]
  simp only [GRH.centeredSquarefreeBilinear, term, Finset.mul_sum, mul_assoc]

theorem term_swap (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (p : ℕ × ℕ) :
    term q a N p.swap = term q a N p := by
  rcases p with ⟨d,e⟩
  simp [term, GRH.squarefreeProgressionCount, and_comm, mul_comm]

private lemma abs_liouville_of_pos {d : ℕ} (hd : 0 < d) :
    |(ArithmeticFunction.liouville d : ℝ)| = 1 := by
  rw [ArithmeticFunction.liouville_apply hd.ne']
  push_cast
  simp [abs_pow]

/-- Absolute sum over a set of maximum row and column degree Δ. -/
theorem abs_sparse_of_discrepancy (q : ℕ) [NeZero q] (a : ZMod q) (N Δ : ℕ)
    (S : Finset (ℕ × ℕ)) (hS : S ⊆ box N.sqrt)
    (hr : ∀ k ∈ Ioc 0 N.sqrt, (S.filter (fun p ↦ p.1 = k)).card ≤ Δ)
    (hc : ∀ k ∈ Ioc 0 N.sqrt, (S.filter (fun p ↦ p.2 = k)).card ≤ Δ)
    (hpoint : ∀ d e : ℕ, 0 < d → 0 < e → d*e ≤ N →
      |GRH.squarefreeProgressionCount q a N d e -
        (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
          GRH.squarefreeProgressionDensity q * (N : ℝ) / ((d : ℝ)*e) else 0)| ≤
        5 * Real.sqrt ((N : ℝ) / ((d : ℝ)*e))) :
    (∑ p ∈ S, |term q a N p|) ≤ 5 * Real.sqrt N * Δ * (1 + Real.log N.sqrt) := by
  have hp (p : ℕ × ℕ) (h : p ∈ S) :
      |term q a N p| ≤ (5 * Real.sqrt N) / Real.sqrt ((p.1 : ℝ) * p.2) := by
    obtain ⟨hd,he⟩ := Finset.mem_product.mp (hS h)
    obtain ⟨hd0,hdU⟩ := Finset.mem_Ioc.mp hd
    obtain ⟨he0,heU⟩ := Finset.mem_Ioc.mp he
    have hprod := (Nat.mul_le_mul hdU heU).trans (Nat.sqrt_le N)
    simpa only [term, abs_mul, abs_liouville_of_pos hd0, abs_liouville_of_pos he0,
      one_mul, Real.sqrt_div (Nat.cast_nonneg N), mul_div_assoc] using hpoint p.1 p.2 hd0 he0 hprod
  have hb := CenteredMatching.abs_sum_le (K := 5 * Real.sqrt N)
    (fun p ↦ |term q a N p|) hS hr hc (by positivity) (by simpa only [abs_abs] using hp)
  rwa [abs_of_nonneg (Finset.sum_nonneg fun p _ ↦ abs_nonneg _)] at hb

end MeadowlarkSquarefree
end

section
open Finset
open scoped BigOperators

namespace GRH

/-- Every fixed row in the width-W diagonal strip has at most 2W+1 points. -/
theorem diagonal_band_row_card_le (U W d : ℕ) :
    ((((Ioc 0 U) ×ˢ (Ioc 0 U)).filter (fun p : ℕ × ℕ =>
      p.1 ≤ p.2 + W ∧ p.2 ≤ p.1 + W)).filter (fun p => p.1 = d)).card ≤ 2*W+1 := by
  apply le_trans (b := (Icc (d-W) (d+W)).card)
  · apply card_le_card_of_injOn Prod.snd
    · intro p hp
      obtain ⟨hband, hr⟩ := mem_filter.mp hp
      obtain ⟨-, hlo, hhi⟩ := mem_filter.mp hband
      apply mem_Icc.mpr
      omega
    · intro p hp r hr h
      exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hr).2.symm) h
  · rw [Nat.card_Icc]
    omega

/-- The same bound holds with the second coordinate fixed. -/
theorem diagonal_band_col_card_le (U W e : ℕ) :
    ((((Ioc 0 U) ×ˢ (Ioc 0 U)).filter (fun p : ℕ × ℕ =>
      p.1 ≤ p.2 + W ∧ p.2 ≤ p.1 + W)).filter (fun p => p.2 = e)).card ≤ 2*W+1 := by
  apply le_trans (b := (Icc (e-W) (e+W)).card)
  · apply card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hband, hr⟩ := mem_filter.mp hp
      obtain ⟨-, hlo, hhi⟩ := mem_filter.mp hband
      apply mem_Icc.mpr
      omega
    · intro p hp r hr h
      exact Prod.ext h ((mem_filter.mp hp).2.trans (mem_filter.mp hr).2.symm)
  · rw [Nat.card_Icc]
    omega

/-- Transposition identifies the two complementary strict half-strips. -/
theorem off_diagonal_band_sum_eq_twice (U W : ℕ) (f : ℕ × ℕ → ℝ)
    (hsym : ∀ d e, f (d,e) = f (e,d)) :
    (∑ p ∈ ((Ioc 0 U) ×ˢ (Ioc 0 U)).filter (fun p : ℕ × ℕ =>
      ¬(p.1 ≤ p.2+W ∧ p.2 ≤ p.1+W)), f p) =
    2 * (∑ p ∈ ((Ioc 0 U) ×ˢ (Ioc 0 U)).filter (fun p : ℕ × ℕ =>
      p.1+W < p.2), f p) := by
  let B := (Ioc 0 U) ×ˢ (Ioc 0 U)
  let L := B.filter (fun p : ℕ × ℕ => p.2+W < p.1)
  let R := B.filter (fun p : ℕ × ℕ => p.1+W < p.2)
  have split : B.filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2+W ∧ p.2 ≤ p.1+W)) = L ∪ R := by
    ext p
    simp only [L,R,mem_union,mem_filter]
    constructor
    · intro ⟨hp,hs⟩
      rcases lt_or_ge (p.2+W) p.1 with h|h
      · exact Or.inl ⟨hp,h⟩
      · exact Or.inr ⟨hp,by omega⟩
    · intro h
      rcases h with ⟨hp,hh⟩|⟨hp,hh⟩ <;> exact ⟨hp,by omega⟩
  have dis : Disjoint L R := by
    refine disjoint_left.mpr ?_
    intro p hl hr
    have h₁ := (mem_filter.mp hl).2
    have h₂ := (mem_filter.mp hr).2
    omega
  have symm_sum : ∑ p ∈ L, f p = ∑ p ∈ R, f p := by
    apply sum_equiv (Equiv.prodComm ℕ ℕ)
    · rintro ⟨d,e⟩
      simp [L,R,B,and_comm,and_left_comm,and_assoc]
    · rintro ⟨d,e⟩ _
      exact hsym d e
  change ∑ p ∈ B.filter _, f p = 2 * ∑ p ∈ R, f p
  rw [split, sum_union dis, symm_sum, two_mul]

/-- The entire square splits into its central band and twice its strict upper part. -/
theorem box_sum_eq_diagonal_band_add_twice (U W : ℕ) (f : ℕ × ℕ → ℝ)
    (hsym : ∀ d e, f (d,e) = f (e,d)) :
    (∑ p ∈ (Ioc 0 U) ×ˢ (Ioc 0 U), f p) =
    (∑ p ∈ ((Ioc 0 U) ×ˢ (Ioc 0 U)).filter (fun p : ℕ × ℕ =>
      p.1 ≤ p.2+W ∧ p.2 ≤ p.1+W), f p) +
    2 * (∑ p ∈ ((Ioc 0 U) ×ˢ (Ioc 0 U)).filter (fun p : ℕ × ℕ =>
      p.1+W < p.2), f p) := by
  rw [← off_diagonal_band_sum_eq_twice U W f hsym]
  exact (sum_filter_add_sum_filter_not _ _ _).symm

end GRH
end

section
open Finset
open scoped BigOperators Classical

namespace MeadowlarkSquarefree

noncomputable def wideWidth (N : ℕ) (σ : ℝ) : ℕ :=
  ⌊((N : ℝ) + 1) ^ (σ - 1/2) / (1 + Real.log (N.sqrt : ℝ))⌋₊

noncomputable def wideNearSum (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (box N.sqrt).filter (fun p : ℕ × ℕ =>
    p.1 ≤ p.2 + wideWidth N σ ∧ p.2 ≤ p.1 + wideWidth N σ), term q a N p

noncomputable def wideUpperSum (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ (box N.sqrt).filter (fun p : ℕ × ℕ => p.1 + wideWidth N σ < p.2), term q a N p

theorem wide_near_add_twice_upper (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (σ : ℝ) :
    GRH.centeredSquarefreeBilinear q a N = wideNearSum q a N σ + 2 * wideUpperSum q a N σ := by
  rw [sum_box]
  exact GRH.box_sum_eq_diagonal_band_add_twice _ _ _ (fun d e => (term_swap q a N (d,e)).symm)

theorem wide_abs_power_of_discrepancy (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ)
    (σ : ℝ) (hσ : 1/2 < σ)
    (hpoint : ∀ d e : ℕ, 0 < d → 0 < e → d*e ≤ N →
      |GRH.squarefreeProgressionCount q a N d e -
        (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
          GRH.squarefreeProgressionDensity q * (N : ℝ) / ((d : ℝ)*e) else 0)| ≤
        5 * Real.sqrt ((N : ℝ) / ((d : ℝ)*e))) :
    (∑ p ∈ (box N.sqrt).filter (fun p : ℕ × ℕ =>
      p.1 ≤ p.2 + wideWidth N σ ∧ p.2 ≤ p.1 + wideWidth N σ), |term q a N p|) ≤ (10 + 5 * (1 + (σ - 1/2)⁻¹)) * ((N:ℝ)+1)^σ := by
  let X : ℝ := (N:ℝ) + 1
  let L := 1 + Real.log (N.sqrt : ℝ)
  let W := wideWidth N σ
  let S := (box N.sqrt).filter (fun p : ℕ × ℕ => p.1 ≤ p.2+W ∧ p.2 ≤ p.1+W)
  have hX : 0 < X := by dsimp [X]; positivity
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_natCast_nonneg N.sqrt]
  have hpow := Real.rpow_pos_of_pos hX (σ-1/2)
  have hfloor : (W:ℝ) ≤ X^(σ-1/2)/L := Nat.floor_le (div_nonneg hpow.le hL.le)
  have hw : (W:ℝ) * L ≤ X^(σ-1/2) := (le_div_iff₀ hL).mp hfloor
  have hsqrt : Real.sqrt (N:ℝ) ≤ X^(1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow (Nat.cast_nonneg N) _ (by norm_num)
    dsimp [X]; linarith
  have hwidth : Real.sqrt N * ((W:ℝ)*L) ≤ X^σ := by
    calc _ ≤ X^(1/2:ℝ) * X^(σ-1/2) := mul_le_mul hsqrt hw (by positivity) (Real.rpow_nonneg hX.le _)
         _ = _ := by rw [← Real.rpow_add hX]; congr 1; ring
  have hrest : Real.sqrt N * L ≤ (1 + (σ-1/2)⁻¹) * X^σ := by
    simpa only [X,L,Real.rpow_zero,mul_one,add_zero] using
      (CenteredMatching.sqrt_mul_rpow_log_le N (α:=0) (σ:=σ) (by simpa only [add_zero] using hσ))
  have hsmall := abs_sparse_of_discrepancy q a N (2*W+1) S (Finset.filter_subset _ _)
    (fun k _ => GRH.diagonal_band_row_card_le _ _ k)
    (fun k _ => GRH.diagonal_band_col_card_le _ _ k) hpoint
  calc
    (∑ p ∈ S, |term q a N p|) ≤ 5 * Real.sqrt N * ((2*W+1:ℕ):ℝ) * L := hsmall
    _ = 10 * (Real.sqrt N * ((W:ℝ)*L)) + 5 * (Real.sqrt N * L) := by push_cast; ring
    _ ≤ 10 * X^σ + 5 * ((1+(σ-1/2)⁻¹) * X^σ) := by linarith only [hwidth,hrest]
    _ = _ := by dsimp only [X]; ring

end MeadowlarkSquarefree
end


open MeadowlarkSquarefree

theorem MeadowlarkSquarefree.verified_wide_band_abs (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (N : ℕ) (σ : ℝ) (hσ : 1/2 < σ) :
    (∑ p ∈ (box N.sqrt).filter (fun p : ℕ × ℕ =>
      p.1 ≤ p.2 + wideWidth N σ ∧ p.2 ≤ p.1 + wideWidth N σ), |term q a N p|) ≤ (10 + 5 * (1 + (σ - 1/2)⁻¹)) * ((N:ℝ)+1)^σ :=
  wide_abs_power_of_discrepancy q a N σ hσ (GRH.squarefreeProgressionCount_error q a ha N)

theorem MeadowlarkSquarefree.verified_wide_near_bound (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (N : ℕ) (σ : ℝ) (hσ : 1/2 < σ) :
    |wideNearSum q a N σ| ≤ (10 + 5 * (1 + (σ - 1/2)⁻¹)) * ((N:ℝ)+1)^σ :=
  (Finset.abs_sum_le_sum_abs _ _).trans (verified_wide_band_abs q a ha N σ hσ)


/- Truncation: meadowlark. Centering: pragyan. Square-divisor transfer: Yi. -/
/-!
This adapts the square-root truncation of Helfgott–Thompson, §2, (2.1), to Liouville coefficients.
The inverse kernel is the indicator of squarefree positive integers.
The weighted divisor-pair argument adapts the reindexing in Mathlib's
ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (ArithmeticFunction/Misc.lean, Apache 2.0,
copyright 2020 Aaron Anderson). 
-/

open scoped BigOperators
open Finset

namespace LiouvilleProgression

abbrev lambda : ArithmeticFunction ℝ := ArithmeticFunction.liouville
noncomputable def squarefreeKernel : ArithmeticFunction ℝ :=
  ⟨fun k => if Squarefree k then 1 else 0, by simp⟩

private theorem kernel_twist (n : ℕ) :
    squarefreeKernel n = lambda n * (ArithmeticFunction.moebius n : ℝ) := by
  change (if Squarefree n then 1 else 0) =
    (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.moebius n : ℝ)
  by_cases h : Squarefree n
  · have heq : ArithmeticFunction.liouville n = ArithmeticFunction.moebius n := by
      rw [ArithmeticFunction.liouville_apply h.ne_zero, ArithmeticFunction.moebius_apply_of_squarefree h]
    rw [if_pos h, heq, ← sq, ← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree h]
    simp
  · simp [h]

-- Twisting the Möbius inverse relation by the completely multiplicative λ gives λ * μ² = 1.
theorem liouville_mul_squarefree : lambda * squarefreeKernel = 1 := by
  ext n
  let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  have hz : z * m = 1 := ArithmeticFunction.coe_zeta_mul_coe_moebius
  rw [ArithmeticFunction.mul_apply]
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal, lambda n * (z p.1 * m p.2) := by
      refine sum_congr rfl fun p hp => ?_
      obtain ⟨hp',hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hfst : p.1 ≠ 0 := by intro h; simp [h] at hp'; exact hn hp'.symm
      have hz1 : z p.1 = 1 := by simp [z, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne hfst]
      have hl : lambda n = lambda p.1 * lambda p.2 := by
        simp [← hp', lambda, ArithmeticFunction.intCoe_apply, ArithmeticFunction.liouville_apply_mul]
      rw [kernel_twist, hz1, hl, one_mul]
      change _ = _ * (ArithmeticFunction.moebius p.2 : ℝ)
      ring
    _ = lambda n * (z * m) n := by rw [ArithmeticFunction.mul_apply, mul_sum]
    _ = _ := by
      rw [hz, ArithmeticFunction.one_apply]
      by_cases h : n = 1 <;> simp [h, lambda, ArithmeticFunction.intCoe_apply,
        ArithmeticFunction.liouville_apply_one]

noncomputable def short (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k ≤ u then (ArithmeticFunction.liouville k : ℝ) else 0, by simp⟩

-- Two factors above the square-root cutoff cannot have product at most n.
private theorem tail_square_zero (n k : ℕ) (hk : k ≤ n) :
    ((lambda - short n.sqrt) * (lambda - short n.sqrt)) k = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hsmall : p.1 ≤ n.sqrt ∨ p.2 ≤ n.sqrt := by
    by_contra! h
    have hh := Nat.mul_le_mul h.1 h.2
    have hn := Nat.lt_succ_sqrt n
    omega
  change ((ArithmeticFunction.liouville p.1 : ℝ) - (if p.1 ≤ n.sqrt then _ else 0)) *
      ((ArithmeticFunction.liouville p.2 : ℝ) - (if p.2 ≤ n.sqrt then _ else 0)) = 0
  rcases hsmall with h | h <;> simp [h]

theorem truncated_coefficient (n k : ℕ) (hk : k ≤ n) :
    lambda k = short n.sqrt k + short n.sqrt k - (short n.sqrt * (short n.sqrt * squarefreeKernel)) k := by
  let s := short n.sqrt
  have hinv : lambda * squarefreeKernel = 1 := liouville_mul_squarefree
  have halg : (lambda - s) * (lambda - s) * squarefreeKernel = lambda - s - s + s * (s * squarefreeKernel) := by
    calc
      _ = lambda * (lambda * squarefreeKernel) - s * (lambda * squarefreeKernel) - s * (lambda * squarefreeKernel) + s * (s * squarefreeKernel) := by ring
      _ = _ := by rw [hinv]; simp
  have hzero : ((lambda - s) * (lambda - s) * squarefreeKernel) k = 0 := by
    rw [ArithmeticFunction.mul_apply]
    refine sum_eq_zero fun p hp => ?_
    obtain ⟨hprod, hk0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : p.1 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) ⟨p.2, hprod.symm⟩
    rw [show ((lambda - s) * (lambda - s)) p.1 = 0 from tail_square_zero n p.1 (hp1.trans hk), zero_mul]
  rw [halg] at hzero
  change lambda k - s k - s k + (s * (s * squarefreeKernel)) k = 0 at hzero
  change lambda k = s k + s k - (s * (s * squarefreeKernel)) k
  linarith

-- Weighted version of the divisor-pair reindexing in Mathlib's
-- ArithmeticFunction.sum_Ioc_mul_eq_sum_sum. The weight need not be multiplicative.
private theorem weighted_convolution (n : ℕ) (w : ℕ → ℝ) (f g : ArithmeticFunction ℝ) :
    (∑ k ∈ Ioc 0 n, w k * (f * g) k) =
    ∑ d ∈ Ioc 0 n, f d * ∑ e ∈ Ioc 0 (n / d), w (d * e) * g e := by
  classical
  let box := (Ioc 0 n) ×ˢ (Ioc 0 n)
  calc
    _ = ∑ k ∈ Ioc 0 n, ∑ p ∈ box, if p.1 * p.2 = k then
          w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      refine sum_congr rfl fun k hk => ?_
      obtain ⟨hk0, hkn⟩ := mem_Ioc.mp hk
      rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk0.ne' hkn,
        mul_sum, ← sum_filter]
      refine sum_congr rfl fun p hp => ?_
      rw [(mem_filter.mp hp).2]
    _ = ∑ p ∈ box, if p.1 * p.2 ≤ n then w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      rw [sum_comm]
      refine sum_congr rfl fun p hp => ?_
      have hp' := mem_product.mp hp
      have hpos := Nat.mul_pos (mem_Ioc.mp hp'.1).1 (mem_Ioc.mp hp'.2).1
      simp [mem_Ioc, hpos]
    _ = _ := by
      rw [show box = _ from rfl, sum_product]
      refine sum_congr rfl fun d hd => ?_
      have hd0 := (mem_Ioc.mp hd).1
      rw [mul_sum]
      have heq : (Ioc 0 (n / d)) = (Ioc 0 n).filter (fun e => d * e ≤ n) := by
        ext e
        simp only [mem_Ioc, mem_filter]
        rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm e d]
        constructor
        · rintro ⟨he, h⟩
          exact ⟨⟨he, ((Nat.le_div_iff_mul_le hd0).mpr (by simpa [Nat.mul_comm] using h)).trans
            (Nat.div_le_self n d)⟩, h⟩
        · rintro ⟨⟨he, _⟩, h⟩
          exact ⟨he, h⟩
      rw [heq, sum_filter]
      apply sum_congr rfl
      intro e _
      dsimp only
      split_ifs <;> ring

private theorem truncate_sum (N u : ℕ) (hu : u ≤ N) (F : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N, short u k * F k) = ∑ k ∈ Ioc 0 u, lambda k * F k := by
  calc
    _ = ∑ k ∈ Ioc 0 u, short u k * F k := by
      symm
      apply sum_subset
      · intro k hk
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hu⟩
      · intro k hk hk'
        have h : ¬ k ≤ u := fun h => hk' (mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,h⟩)
        simp [short, h]
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      simp [short, (mem_Ioc.mp hk).2, lambda]

noncomputable def residueWeight {q : ℕ} (a : ZMod q) (k : ℕ) : ℝ :=
  if (k : ZMod q) = a then 1 else 0

noncomputable def bilinear {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n.sqrt, lambda d * ∑ e ∈ Ioc 0 n.sqrt, lambda e *
    (((Ioc 0 (n / (d * e))).filter (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

theorem reindex_bilinear {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ Ioc 0 n, residueWeight a k * (short n.sqrt * (short n.sqrt * squarefreeKernel)) k) =
    bilinear a n := by
  rw [weighted_convolution, truncate_sum n _ (Nat.sqrt_le_self n)]
  refine sum_congr rfl fun d hd => ?_
  have hd' := mem_Ioc.mp hd
  have hu : n.sqrt ≤ n / d := (Nat.le_div_iff_mul_le hd'.1).mpr <|
    (Nat.mul_le_mul_left n.sqrt hd'.2).trans (Nat.sqrt_le n)
  congr 1
  rw [weighted_convolution (n / d) (fun k => residueWeight a (d * k)), truncate_sum _ _ hu]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  rw [Nat.div_div_eq_div_mul, ← sum_boole]
  refine sum_congr rfl fun r hr => ?_
  by_cases hs : Squarefree r <;> by_cases h : ((d * e * r : ℕ) : ZMod q) = a <;>
    simp_all [residueWeight, squarefreeKernel, Nat.mul_assoc]

noncomputable def partialSum {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 n, lambda k * residueWeight a k

theorem weighted_identity {q : ℕ} (a : ZMod q) (n : ℕ) :
    partialSum a n = 2 * partialSum a n.sqrt - bilinear a n := by
  unfold partialSum
  rw [← reindex_bilinear, ← truncate_sum n _ (Nat.sqrt_le_self n)]
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [truncated_coefficient n k (mem_Ioc.mp hk).2]
  ring

theorem parent_sum {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      if (k : ZMod q) = a then (ArithmeticFunction.liouville k : ℝ) else 0) = partialSum a n := by
  classical
  have hr : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hr, sum_insert (by simp)]
  have hz : (ArithmeticFunction.liouville 0 : ℝ) = 0 := by simp
  simp only [hz, ite_self, zero_add]
  refine sum_congr rfl fun k _ => ?_
  simp only [residueWeight, lambda, ArithmeticFunction.intCoe_apply]
  split_ifs <;> simp_all


end LiouvilleProgression

open scoped BigOperators
open Finset

private theorem factored_sum {α : Type*} (s : Finset α) (l h : α → ℝ) (K : ℝ) :
    (∑ d ∈ s, l d * ∑ e ∈ s, l e * (K * h d * h e)) =
      K * (∑ d ∈ s, l d * h d) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem centered_sum {α : Type*} (s : Finset α) (l h : α → ℝ)
    (A : α → α → ℝ) (K : ℝ) :
    (∑ d ∈ s, l d * ∑ e ∈ s, l e * A d e) =
      (∑ d ∈ s, l d * ∑ e ∈ s, l e * (A d e - K * h d * h e)) +
        K * (∑ d ∈ s, l d * h d) ^ 2 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [factored_sum]
  ring


theorem GRH.squarefree_bilinear_eq_centered
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
        (((Finset.Ioc 0 (N / (d * e))).filter
          (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)) =
      GRH.centeredSquarefreeBilinear q a N +
        GRH.squarefreeProgressionDensity q * (N : ℝ) *
          (GRH.reducedLiouvilleHarmonic q N.sqrt) ^ 2 := by
  classical
  let h : ℕ → ℝ := fun d => if IsUnit (d : ZMod q) then 1 / (d : ℝ) else 0
  have harmonic :
      (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) * h d) =
        GRH.reducedLiouvilleHarmonic q N.sqrt := by
    unfold GRH.reducedLiouvilleHarmonic
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hu : IsUnit (d : ZMod q) <;> simp [h, hu, div_eq_mul_inv]
  have kernel (d e : ℕ) :
      (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        GRH.squarefreeProgressionDensity q * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      (GRH.squarefreeProgressionDensity q * (N : ℝ)) * h d * h e := by
    by_cases hd : IsUnit (d : ZMod q) <;> by_cases he : IsUnit (e : ZMod q) <;>
      simp [h, hd, he, div_eq_mul_inv, mul_inv_rev] <;> ring
  change (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.liouville e : ℝ) *
        GRH.squarefreeProgressionCount q a N d e) = _
  unfold GRH.centeredSquarefreeBilinear
  simp_rw [kernel]
  rw [← harmonic]
  exact centered_sum (Finset.Ioc 0 N.sqrt)
    (fun d => (ArithmeticFunction.liouville d : ℝ)) h
    (GRH.squarefreeProgressionCount q a N) (GRH.squarefreeProgressionDensity q * (N : ℝ))


namespace GRH

lemma sqrt_rpow_weight_bound (N : ℕ) (σ : ℝ) (hone : σ < 1) :
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤ ((N : ℝ) + 1) ^ σ := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hU : 0 < (N.sqrt : ℝ) + 1 := by positivity
  have hX : 0 < (N : ℝ) + 1 := by positivity
  have hsqrt : (N : ℝ) + 1 ≤ ((N.sqrt : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt' N
    have h' : N + 1 ≤ (N.sqrt + 1) ^ 2 := by simpa [Nat.succ_eq_add_one] using Nat.succ_le_iff.mpr h
    exact_mod_cast h'
  have hp : (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 ≤
      ((N : ℝ) + 1) ^ (σ - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos hX hsqrt (by linarith : σ - 1 ≤ 0)
    rw [← Real.rpow_natCast_mul hU.le] at h
    rw [← Real.rpow_mul_natCast hU.le]
    convert h using 1 <;> congr 1 <;> ring
  calc
    (N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2
        ≤ (N : ℝ) * (((N : ℝ) + 1) ^ (σ - 1)) := mul_le_mul_of_nonneg_left hp hN
    _ ≤ ((N : ℝ) + 1) * (((N : ℝ) + 1) ^ (σ - 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hX.le _)
    _ = ((N : ℝ) + 1) ^ σ := by
      nth_rw 1 [← Real.rpow_one ((N : ℝ) + 1)]
      rw [← Real.rpow_add hX]
      congr 1
      ring

lemma harmonic_main_weight_bound (N : ℕ) (σ K x : ℝ) (hone : σ < 1)
    (hK : 0 ≤ K) (hx : |x| ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1)) :
    (N : ℝ) * x ^ 2 ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ := by
  have hs : x ^ 2 ≤ K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2 := by
    have h := sq_le_sq₀ (abs_nonneg x) (by positivity : 0 ≤ K * ((N.sqrt : ℝ) + 1) ^ (σ - 1))
    have := h.mpr hx
    simpa only [sq_abs, mul_pow] using this
  calc
    (N : ℝ) * x ^ 2 ≤ (N : ℝ) *
        (K ^ 2 * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg N)
    _ = K ^ 2 * ((N : ℝ) * (((N.sqrt : ℝ) + 1) ^ (σ - 1)) ^ 2) := by ring
    _ ≤ K ^ 2 * ((N : ℝ) + 1) ^ σ :=
      mul_le_mul_of_nonneg_left (sqrt_rpow_weight_bound N σ hone) (sq_nonneg K)

end GRH


open Finset ArithmeticFunction

private theorem squarefree_core_root_unique {r d a b : ℕ} (hr : r ≠ 0) (hd : d ≠ 0)
    (ha : Squarefree a) (hb : Squarefree b) (h : r^2 * a = d^2 * b) : r = d := by
  apply Nat.eq_of_factorization_eq hr hd
  intro p
  have he := congrArg (fun n : ℕ ↦ n.factorization p) h
  simp only [Nat.factorization_mul (pow_ne_zero _ hr) ha.ne_zero,
    Nat.factorization_mul (pow_ne_zero _ hd) hb.ne_zero, Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at he
  have h₁ := ha.natFactorization_le_one p
  have h₂ := hb.natFactorization_le_one p
  omega

private theorem liouville_square_unit {r : ℕ} (hr : r ≠ 0) : liouville (r^2) = 1 := by
  rw [pow_two, liouville_apply_mul, liouville_apply hr, ←pow_two, ←pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem GRH.liouville_eq_sum_square_divisor_moebius (n N : ℕ) (hnN : n ≤ N) :
    liouville n = ∑ d ∈ range (N+1), if d^2 ∣ n then moebius (n/d^2) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨a,r,ha,hr,hra,hsq⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hn)
  have hdiv : r ^ 2 ∣ n := ⟨a, hra.symm⟩
  have hrmem : r ∈ range (N+1) := by
    apply mem_range.mpr
    have hrn := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ((dvd_pow_self r two_ne_zero).trans hdiv)
    omega
  rw [Finset.sum_eq_single_of_mem r hrmem]
  · rw [if_pos hdiv, ←hra, Nat.mul_div_cancel_left _ (pow_pos hr _), liouville_apply_mul,
      liouville_square_unit hr.ne', one_mul, moebius_apply_of_squarefree hsq, liouville_apply ha.ne']
  · intro d _ hdr
    split_ifs with hdvd
    · apply moebius_eq_zero_of_not_squarefree
      intro hb
      have hd : d ≠ 0 := by rintro rfl; simp [hn] at hdvd
      exact hdr (squarefree_core_root_unique hr.ne' hd hsq hb (hra.trans (Nat.mul_div_cancel' hdvd).symm)).symm
    · rfl

private theorem sum_multiples_le {t : ℕ} (ht : 0 < t) (N : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ range (N + 1), if t ∣ k then f k else 0) = ∑ j ∈ range (N / t + 1), f (t*j) := by
  rw [← sum_filter]
  apply sum_bij' (fun k _ ↦ k / t) (fun j _ ↦ t * j)
  · intro k hk
    exact mem_range.mpr <| Nat.lt_succ_of_le <| Nat.div_le_div_right <| Nat.le_of_lt_succ <| mem_range.mp (mem_filter.mp hk).1
  · intro j hj
    apply mem_filter.mpr
    refine ⟨mem_range.mpr <| Nat.lt_succ_of_le ?_, dvd_mul_right _ _⟩
    simpa [mul_comm] using (Nat.le_div_iff_mul_le ht).mp (Nat.le_of_lt_succ (mem_range.mp hj))
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro j _
    exact Nat.mul_div_cancel_left j ht
  · intro k hk
    rw [Nat.mul_div_cancel' (mem_filter.mp hk).2]

theorem GRH.liouville_progression_square_sieve (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (∑ k ∈ range (N+1), if (k : ZMod q) = a then (liouville k : ℝ) else 0) =
    ∑ d ∈ range (N+1), ∑ j ∈ range (N/d^2+1),
      if ((d^2*j : ℕ) : ZMod q) = a then (moebius j : ℝ) else 0 := by
  classical
  let f (d k : ℕ) : ℝ := if (k : ZMod q) = a then (moebius (k / d^2) : ℝ) else 0
  calc _ = ∑ k ∈ range (N+1), ∑ d ∈ range (N+1), if d^2 ∣ k then f d k else 0 := by
            apply sum_congr rfl
            intro k hk
            by_cases h : (k : ZMod q) = a
            · simp only [f, h, if_true]
              exact_mod_cast GRH.liouville_eq_sum_square_divisor_moebius k N (Nat.le_of_lt_succ (mem_range.mp hk))
            · simp [f, h]
       _ = ∑ d ∈ range (N+1), ∑ k ∈ range (N+1), if d^2 ∣ k then f d k else 0 := sum_comm
       _ = _ := by
            apply sum_congr rfl
            intro d hd
            by_cases hd0 : d = 0
            · simp [hd0, f]
            rw [sum_multiples_le (pow_pos (Nat.pos_of_ne_zero hd0) _) N (f d)]
            simp only [f, Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_ne_zero hd0) _)]

open Finset ArithmeticFunction

private theorem bound_permuted_class (f : ℕ → ℝ) (q : ℕ) [NeZero q] (a t : ZMod q) (ha : IsUnit a)
    (N : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (H : ∀ c : ZMod q, IsUnit c →
      |∑ j ∈ range (N+1), if (j:ZMod q) = c then (f j) else 0| ≤ b) :
    |∑ j ∈ range (N+1), if t*(j:ZMod q) = a then (f j) else 0| ≤ b := by
  classical
  by_cases ht : IsUnit t
  · let u := ht.unit
    have hu : (u : ZMod q) = t := ht.unit_spec
    let c : ZMod q := (↑u⁻¹ : ZMod q)*a
    have hc : IsUnit c := u⁻¹.isUnit.mul ha
    have hi (j : ℕ) : t*(j:ZMod q) = a ↔ (j:ZMod q) = c := by
      rw [←hu]
      change (u : ZMod q) * (j : ZMod q) = a ↔ (j : ZMod q) = (↑u⁻¹ : ZMod q) * a
      constructor
      · intro h
        exact ((u.inv_mul_eq_iff_eq_mul).mpr h.symm).symm
      · intro h
        exact ((u.inv_mul_eq_iff_eq_mul).mp h.symm).symm
    simpa only [hi] using H c hc
  · have hn (j : ℕ) : t*(j:ZMod q) ≠ a := fun h => ht (isUnit_of_mul_isUnit_left (h ▸ ha))
    simpa [hn] using hb


theorem GRH.square_divisor_progression_bound (f : ℕ → ℝ) (hf0 : f 0 = 0)
    (q : ℕ) [NeZero q] (σ C : ℝ) (hσ : 1/2 < σ) (hC : 0 ≤ C)
    (H : ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then f j else 0| ≤ C*((N:ℝ)+1)^σ)
    (a : ZMod q) (ha : IsUnit a) (N : ℕ) :
    |∑ d ∈ range (N+1), ∑ j ∈ range (N/d^2+1),
      if ((d^2*j:ℕ):ZMod q) = a then f j else 0| ≤
      (C * (2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹) * ((N:ℝ)+1)^σ := by
  classical
  let w (d : ℕ) := ((d:ℝ)^(2*σ))⁻¹
  have hσ0 : 0 ≤ σ := by linarith
  have hsum : Summable w := Real.summable_nat_rpow_inv.mpr (by linarith)
  have hw (d : ℕ) : 0 ≤ w d := by dsimp [w]; positivity
  let K := C*(2:ℝ)^σ*((N:ℝ)+1)^σ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ range (N+1), K*w d := by
          apply sum_le_sum
          intro d hd
          by_cases hd0 : d = 0
          · simpa [hd0,hf0] using mul_nonneg hK (hw 0)
          by_cases hdn : d^2 ≤ N
          · let t : ZMod q := (d^2 : ℕ)
            have hperm := bound_permuted_class f q a t ha (N/d^2) (C*((N/d^2:ℕ)+1:ℝ)^σ)
              (by positivity) (fun c hc => H c hc _)
            have ht (j : ℕ) : ((d^2*j:ℕ):ZMod q) = t*(j:ZMod q) := by simp [t]
            simp_rw [ht]
            apply hperm.trans
            have hdpos : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_ne_zero hd0
            have hds : (0:ℝ)<(d:ℝ)^2 := sq_pos_of_pos hdpos
            have hdiv : (N/d^2:ℕ) ≤ (N:ℝ)/(d:ℝ)^2 := by
              apply (le_div_iff₀ hds).mpr
              exact_mod_cast Nat.div_mul_le_self N (d^2)
            have hsN : (d:ℝ)^2 ≤ N := by exact_mod_cast hdn
            have hx : (N/d^2:ℕ)+1 ≤ (2*((N:ℝ)+1))/(d:ℝ)^2 := by
              apply (le_div_iff₀ hds).mpr
              have hb := (le_div_iff₀ hds).mp hdiv
              nlinarith
            have hp := Real.rpow_le_rpow (by positivity) hx hσ0
            apply (mul_le_mul_of_nonneg_left hp hC).trans_eq
            dsimp [K,w]
            rw [Real.div_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
            have hpower : ((d:ℝ)^2) ^ σ = (d:ℝ)^(2*σ) := by
              rw [Real.rpow_mul hdpos.le]
              norm_num
            rw [hpower]
            ring
          · have hzero : N / d^2 = 0 := Nat.div_eq_of_lt (lt_of_not_ge hdn)
            simp [hzero, hf0, mul_nonneg hK (hw d)]
       _ = K * ∑ d ∈ range (N+1), w d := (mul_sum ..).symm
       _ ≤ K * ∑' d, w d := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun i _ => hw i)) hK
       _ = _ := by dsimp [K,w]; ring

open Asymptotics Filter Finset

theorem SeparatedUpperEvidence.reduced_classes_uniform_real (q : ℕ) [NeZero q] (σ : ℝ) (hσ : 0 ≤ σ)
    (f : ℕ → ℤ)
    (H : ∀ a : ZMod q, IsUnit a →
      (fun N : ℕ => ∑ k ∈ range (N+1), if a = (k : ZMod q) then (f k : ℂ) else 0)
        =O[atTop] (fun N : ℕ => (N : ℝ)^σ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ k ∈ range (N+1), if (k : ZMod q) = a then (f k : ℝ) else 0| ≤ C*((N:ℝ)+1)^σ := by
  classical
  let F (a : ZMod q) (N : ℕ) : ℂ := ∑ k ∈ range (N+1), if a = (k : ZMod q) then (f k : ℂ) else 0
  let R (a : ZMod q) (N : ℕ) : ℝ := ∑ k ∈ range (N+1), if (k : ZMod q) = a then (f k : ℝ) else 0
  have hcast (a : ZMod q) (N : ℕ) : (R a N : ℂ) = F a N := by
    simp only [R, F, Complex.ofReal_sum]
    apply sum_congr rfl
    intro k _
    by_cases hk : (k : ZMod q) = a
    · simp [hk]
    · simp [hk, Ne.symm hk]
  have hscale : (fun n : ℕ => (n:ℝ)^σ) =O[atTop] (fun n : ℕ => ((n:ℝ)+1)^σ) := by
    refine isBigO_of_le _ fun n => ?_
    simp only [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n:ℝ)+1) σ)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hσ
  have hlocal (a : ZMod q) : ∃ D : ℝ, 0 ≤ D ∧
      (IsUnit a → ∀ N : ℕ, |R a N| ≤ D*((N:ℝ)+1)^σ) := by
    by_cases ha : IsUnit a
    · obtain ⟨D,hD,hbound⟩ := bound_of_isBigO_nat_atTop ((H a ha).trans hscale)
      refine ⟨D,hD.le,fun _ N => ?_⟩
      have ht := hbound (x := N) (by positivity)
      change ‖F a N‖ ≤ D * ‖((N:ℝ)+1)^σ‖ at ht
      simpa only [← hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (Real.rpow_nonneg (by positivity : 0 ≤ (N:ℝ)+1) σ)] using ht
    · exact ⟨0, le_rfl, fun h => (ha h).elim⟩
  choose D hD hc using hlocal
  refine ⟨∑ a, D a, sum_nonneg (fun a _ => hD a), fun a ha N => (hc a ha N).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact single_le_sum (fun b _ => hD b) (mem_univ a)

open Finset ArithmeticFunction MeadowlarkSquarefree LiouvilleProgression
open scoped BigOperators
namespace SeparatedUpperEvidence

/-- The two-dimensional signed sum is determined by two ordinary prefixes, the coprime
harmonic density correction and the explicitly controlled band. -/
theorem upper_identity (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) (σ : ℝ) :
    2 * wideUpperSum q a N σ =
      2 * partialSum a N.sqrt - partialSum a N -
      GRH.squarefreeProgressionDensity q * N * (GRH.reducedLiouvilleHarmonic q N.sqrt)^2 -
      wideNearSum q a N σ := by
  have h1 := weighted_identity a N
  have h2 := GRH.squarefree_bilinear_eq_centered q a N
  change bilinear a N = _ at h2
  have h3 := wide_near_add_twice_upper q a N σ
  linarith only [h1,h2,h3]

theorem upper_of_prefix_and_harmonic (q : ℕ) [NeZero q] (σ L K : ℝ)
    (hhalf : 1/2 < σ) (hone : σ < 1) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hprefix : ∀ a : ZMod q, IsUnit a → ∀ N : ℕ, |partialSum a N| ≤ L*((N:ℝ)+1)^σ)
    (harmonic : ∀ U : ℕ, |GRH.reducedLiouvilleHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |wideUpperSum q a N σ| ≤ C*((N:ℝ)+1)^σ := by
  let B := (10+5*(1+(σ-1/2)⁻¹))
  let k := GRH.squarefreeProgressionDensity q
  have hgap : 0 < σ - 1/2 := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(3*L+ |k| * K^2+B)/2, by positivity, ?_⟩
  intro a ha N
  let X := ((N:ℝ)+1)^σ
  have hl : |partialSum a N| ≤ L*X  := hprefix a ha N
  have hs : |partialSum a N.sqrt| ≤ L*X := by
    apply (hprefix a ha N.sqrt).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Real.rpow_le_rpow (by positivity) _ (by linarith)
    exact add_le_add_left (by exact_mod_cast Nat.sqrt_le_self N) _
  have hband : |wideNearSum q a N σ| ≤ B*X := verified_wide_near_bound q a ha N σ hhalf
  have hm : |k*N*(GRH.reducedLiouvilleHarmonic q N.sqrt)^2| ≤ (|k| * K^2)*X := by
    simpa only [abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ N),
      abs_of_nonneg (sq_nonneg (GRH.reducedLiouvilleHarmonic q N.sqrt)),mul_assoc,X] using
      mul_le_mul_of_nonneg_left (GRH.harmonic_main_weight_bound N σ K _ hone hK (harmonic _)) (abs_nonneg k)
  have he := upper_identity q a N σ
  change 2*wideUpperSum q a N σ = 2*partialSum a N.sqrt - partialSum a N - k*N*(GRH.reducedLiouvilleHarmonic q N.sqrt)^2 - wideNearSum q a N σ at he
  change |wideUpperSum q a N σ| ≤ ((3*L+ |k| * K^2+B)/2)*X
  apply abs_le.mpr
  constructor
  · nlinarith only [he,(abs_le.mp hs).1,(abs_le.mp hl).2,(abs_le.mp hm).2,(abs_le.mp hband).2]
  · nlinarith only [he,(abs_le.mp hs).2,(abs_le.mp hl).1,(abs_le.mp hm).1,(abs_le.mp hband).1]

end SeparatedUpperEvidence

open Finset ArithmeticFunction Filter Asymptotics
open scoped BigOperators
namespace SeparatedUpperEvidence

abbrev UniformMobius (q : ℕ) [NeZero q] (β : ℝ) :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
    |∑ n ∈ range (N+1), if (n:ZMod q)=a then (moebius n : ℝ) else 0| ≤ C*((N:ℝ)+1)^β

theorem uniform_of_residues (q : ℕ) [NeZero q] (β : ℝ)
    (h : ∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ n ∈ range (N+1), if (n:ZMod q)=a then (moebius n : ℝ) else 0| ≤ C*((N:ℝ)+1)^β) :
    UniformMobius q β := by
  classical
  have hall (a : ZMod q) : ∃ C : ℝ, 0 ≤ C ∧ (IsUnit a → ∀ N : ℕ,
      |∑ n ∈ range (N+1), if (n:ZMod q)=a then (moebius n : ℝ) else 0| ≤ C*((N:ℝ)+1)^β) := by
    by_cases ha : IsUnit a
    · exact (h a ha).imp (fun c hc => ⟨hc.1,fun _ => hc.2⟩)
    · exact ⟨0, le_rfl, fun hu => (ha hu).elim⟩
  choose C hc hbound using hall
  refine ⟨∑ a, C a, sum_nonneg (fun a _ => hc a), fun a ha N => (hbound a ha N).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (single_le_sum (fun b _ => hc b) (mem_univ a)) (by positivity)

theorem unit_modulus_mertens (β : ℝ) (hβ : 0 ≤ β) (hm : UniformMobius 1 β) :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, (moebius n : ℝ)) =O[atTop] (fun N : ℕ => (N:ℝ)^β) := by
  obtain ⟨C,hC,h⟩ := hm
  apply Asymptotics.IsBigO.of_bound (C*2^β)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  have hr : range (N+1) = insert 0 (Ioc 0 N) := by ext n; simp only [mem_range,mem_insert,mem_Ioc]; omega
  have h₀ := h (1 : ZMod 1) isUnit_one N
  have hc (n : ℕ) : (n : ZMod 1) = 1 := Subsingleton.elim _ _
  simp only [hc,if_true] at h₀
  rw [hr, Finset.sum_insert (by simp : 0 ∉ Ioc 0 N)] at h₀
  simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_add] at h₀
  have hN' : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (N:ℝ)+1) (show (N:ℝ)+1 ≤ 2*N by linarith) hβ
  rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)] at hpow
  rw [Real.norm_eq_abs,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _),he]
  calc _ ≤ C*((N:ℝ)+1)^β := h₀
       _ ≤ C*(2^β*(N:ℝ)^β) := mul_le_mul_of_nonneg_left hpow hC
       _ = _ := by ring

theorem liouville_prefix_of_mobius (q : ℕ) [NeZero q] (σ : ℝ) (hσ : 1/2 < σ)
    (hm : UniformMobius q σ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |LiouvilleProgression.partialSum a N| ≤ L*((N:ℝ)+1)^σ := by
  obtain ⟨C,hC,H⟩ := hm
  refine ⟨C*(2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹, by positivity, ?_⟩
  intro a ha N
  rw [← LiouvilleProgression.parent_sum,GRH.liouville_progression_square_sieve]
  exact GRH.square_divisor_progression_bound (fun k : ℕ => (moebius k : ℝ))
    (by simp) q σ C hσ hC H a ha N

end SeparatedUpperEvidence

open Finset Filter MeasureTheory Topology Asymptotics ArithmeticFunction
open GRH

namespace SeparatedUpperEvidence

/-- Single-exponent form of dga471's Abel-summation argument
(prove2.me/submissions/26c76384-33b3-4805-b323-90fb088f25b6). -/
private theorem moebius_dirichlet_converges (r σ : ℝ) (hr : 0 ≤ r) (hrs : r < σ)
    (hM : (fun N : ℕ ↦ ∑ k ∈ Icc 1 N, (moebius k : ℝ)) =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ r)) :
    ∃ L : ℝ, Tendsto (fun N : ℕ ↦ ∑ n ∈ Icc 1 N, (moebius n : ℝ) * (n : ℝ) ^ (-σ))
      atTop (𝓝 L) := by
  let c : ℕ → ℝ := fun n ↦ (moebius n : ℝ)
  have hc : c 0 = 0 := by simp [c]
  have hsum (N : ℕ) : ∑ k ∈ Icc 0 N, c k = ∑ k ∈ Icc 1 N, c k := by
    rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc]
    simp
  have hO : (fun N => ∑ k ∈ Icc 0 N, c k) =O[atTop] fun N => (N : ℝ) ^ r := by
    simpa only [hsum] using hM
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-σ) * ∑ k ∈ Icc 0 N, c k)
      atTop (𝓝 0) := by
    have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(σ - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hrs)).comp tendsto_natCast_atTop_atTop
    exact (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-σ) r (-(σ - r))
      (isBigO_refl _ _) hO (by linarith)).trans_tendsto hp
  have hfloor : (fun t : ℝ => ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ r :=
    (hO.comp_tendsto tendsto_nat_floor_atTop).trans
      (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  have hdom : (fun t : ℝ => deriv (fun x : ℝ => x ^ (-σ)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ (-σ - 1 + r) :=
    IsBigO.mul_atTop_rpow_of_isBigO_rpow (-σ - 1) r (-σ - 1 + r)
      (isBigO_deriv_rpow_const_atTop (-σ)) hfloor le_rfl
  have hint : LocallyIntegrableOn (deriv (fun x : ℝ => x ^ (-σ))) (Set.Ici 1) := by
    rw [Real.deriv_rpow_const']
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ici
    exact continuousOn_const.mul (fun t ht =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans_le ht).ne')).continuousWithinAt)
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc
    (f := fun x : ℝ => x ^ (-σ))
    (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (zero_lt_one.trans_le ht).ne')
    hint hlim hdom (integrableAtFilter_rpow_atTop_iff.mpr (by linarith : -σ - 1 + r < -1))
  refine ⟨_, hconv.congr (fun N => ?_)⟩
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc, mul_zero, zero_add]
  simp only [zero_add]
  exact sum_congr rfl fun n _ => mul_comm _ _

/-- The bounded-prefix and coprime transfers follow marozols' accepted submission
(prove2.me/submissions/e87e9854-dba7-4bb6-9fe7-e23f23a0a723). The input here needs one exponent. -/
theorem reduced_harmonic_of_moebius_prefix (q : ℕ) [NeZero q] (β σ : ℝ) (hβ : 1/2 < β)
    (hβσ : β < σ) (hone : σ < 1)
    (hM : (fun N : ℕ => ∑ n ∈ Icc 1 N, (moebius n : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ β)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ, |reducedLiouvilleHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by
  classical
  have hhalf : (1/2 : ℝ) < σ := hβ.trans hβσ
  let f (n : ℕ) := (moebius n:ℝ)*(n:ℝ)^(-σ)
  obtain ⟨L,hL⟩ := moebius_dirichlet_converges β σ (by linarith) hβσ hM
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  have hbound (N : ℕ) : |∑ n ∈ range N, f n| ≤ max 0 B := by
    cases N with
    | zero => simp
    | succ N =>
      have he : range (N+1) = insert 0 (Icc 1 N) := by ext k; simp; omega
      rw [he, sum_insert (by simp),show f 0 = 0 by simp [f],zero_add]
      exact (hB ⟨N,rfl⟩).trans (le_max_right ..)
  have hC : 0 ≤ max 0 B := le_max_left .. 
  let Z := ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  let D := ∑ d ∈ q.divisors, |(moebius d:ℝ)| * (d:ℝ)^(-σ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => by positivity)
  have hD : 0 ≤ D := sum_nonneg (fun d _ => by positivity)
  refine ⟨((2 * max 0 B) * Z) * D, by positivity, ?_⟩
  intro U
  apply reduced_liouville_harmonic_le_of_modulus_one q σ _ hone.le (by positivity) _ U
  intro V
  apply liouville_harmonic_le_of_moebius_harmonic_le σ _ hhalf hone.le (by positivity) _ V
  exact moebius_harmonic_decay_of_bounded_dirichlet_prefixes σ _ hone.le hC hbound

end SeparatedUpperEvidence

open Finset ArithmeticFunction MeadowlarkSquarefree
open scoped BigOperators
namespace SeparatedUpperEvidence

theorem upper_from_mobius (q : ℕ) [NeZero q] (β σ : ℝ)
    (hβ : 1/2 < β) (hβσ : β < σ) (hone : σ < 1)
    (hq : UniformMobius q σ) (h1 : UniformMobius 1 β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |wideUpperSum q a N σ| ≤ C*((N:ℝ)+1)^σ := by
  have hhalf := hβ.trans hβσ
  obtain ⟨L,hL,hprefix⟩ := liouville_prefix_of_mobius q σ hhalf hq
  obtain ⟨K,hK,hharm⟩ := reduced_harmonic_of_moebius_prefix q β σ hβ hβσ hone
    (unit_modulus_mertens β (by linarith) h1)
  exact upper_of_prefix_and_harmonic q σ L K hhalf hone hL hK hprefix hharm

theorem uniform_above_record (q : ℕ) [NeZero q] (σ : ℝ)
    (hi : (0.8749570698:ℝ) < σ) : UniformMobius q σ :=
  reduced_classes_uniform_real q σ (by linarith) moebius
    (GRH.mobius_character_and_progression_bounds_above_record q σ hi).2

/-- This entire exponent interval uses only previously proved platform inputs. -/
theorem upper_above_record (q : ℕ) [NeZero q] (σ : ℝ)
    (hi : (0.8749570698:ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |wideUpperSum q a N σ| ≤ C*((N:ℝ)+1)^σ := by
  let β : ℝ := (0.8749570698 + σ)/2
  have hb : (0.8749570698:ℝ) < β := by dsimp [β]; linarith
  exact upper_from_mobius q β σ (by linarith) (by dsimp [β]; linarith) hone
    (uniform_above_record q σ hi) (uniform_above_record 1 β hb)

theorem uniform_below_record (q : ℕ) [NeZero q] (σ : ℝ)
    (hhalf : 1/2 < σ) (hone : σ < 1) (hc : σ ≤ 0.8749570698) :
    UniformMobius q σ :=
  uniform_of_residues q σ (fun a ha =>
    GRH.moebius_partial_sum_reduced_progression_power_bound_below_record q a ha σ hhalf hone hc)

end SeparatedUpperEvidence
open SeparatedUpperEvidence
theorem solution
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      let W : ℕ := ⌊((N : ℝ) + 1) ^ (σ - 1/2) / (1 + Real.log (N.sqrt : ℝ))⌋₊
      |∑ p ∈ (((Finset.Ioc 0 N.sqrt) ×ˢ (Finset.Ioc 0 N.sqrt)).filter
          (fun p : ℕ × ℕ => p.1 + W < p.2)),
        (ArithmeticFunction.liouville p.1 : ℝ) * (ArithmeticFunction.liouville p.2 : ℝ) *
          (GRH.squarefreeProgressionCount q a N p.1 p.2 -
            if IsUnit (p.1 : ZMod q) ∧ IsUnit (p.2 : ZMod q) then
              GRH.squarefreeProgressionDensity q * (N : ℝ) / ((p.1 : ℝ) * p.2)
            else 0)| ≤ C * ((N : ℝ) + 1) ^ σ := by
  by_cases hi : (0.8749570698:ℝ) < σ
  · exact upper_above_record q σ hi hone
  · let β : ℝ := (1/2 + σ)/2
    have hb : 1/2 < β := by dsimp [β]; linarith
    have hbs : β < σ := by dsimp [β]; linarith
    exact upper_from_mobius q β σ hb hbs hone
      (uniform_below_record q σ hhalf hone (le_of_not_gt hi))
      (uniform_below_record 1 β hb (by linarith) (by linarith))
