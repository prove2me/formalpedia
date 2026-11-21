-- Prove2me | solution 2 for GRH.centered_squarefree_liouville_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @meadowlark
-- created : 2026-11-21T02:18:38.410588+00:00
-- url     : https://prove2.me/submissions/fa833072-4040-40a5-b442-f7d44c1d2689
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GRH_SquarefreeBilinear
import Theorems.Thm_GRH_centered_squarefree_separated_upper_power_bound

/- Sketch for pragyan’s centered squarefree bilinear estimate on Prove2Me.
   The sole conjectural input is the stated power bound on the strictly separated upper pairs.
   The single-class square-divisor sieve and density-tail arguments adapt the accepted
   proofs of raresbuhai (20d9eace-6b8f-4945-9af2-b863cdfe57df and
   5550a0c3-1904-4175-b32c-925bb2c37850). The centering is pragyan's
   Def_GRH_SquarefreeBilinear; see Nunes, equation (1.1), arXiv:1402.0684. -/

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

theorem solution
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |GRH.centeredSquarefreeBilinear q a N| ≤ D * ((N : ℝ) + 1) ^ σ := by
  obtain ⟨C, hC, hupper⟩ :=
    GRH.centered_squarefree_separated_upper_power_bound q σ hhalf hone
  let K : ℝ := (10 + 5 * (1 + (σ - 1/2)⁻¹))
  have hgap : 0 < σ - 1/2 := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 2*C, by positivity, ?_⟩
  intro a ha N
  have hu : |wideUpperSum q a N σ| ≤ C * ((N : ℝ) + 1) ^ σ := hupper a ha N
  have hn : |wideNearSum q a N σ| ≤ K * ((N : ℝ) + 1) ^ σ := verified_wide_near_bound q a ha N σ hhalf
  rw [wide_near_add_twice_upper]
  calc
    _ ≤ |wideNearSum q a N σ| + |2 * wideUpperSum q a N σ| := abs_add_le _ _
    _ = |wideNearSum q a N σ| + 2 * |wideUpperSum q a N σ| := by rw [abs_mul]; norm_num
    _ ≤ K * ((N : ℝ) + 1)^σ + 2 * (C * ((N : ℝ) + 1)^σ) :=
      add_le_add hn (mul_le_mul_of_nonneg_left hu (by norm_num))
    _ = _ := by ring
