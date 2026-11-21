-- Prove2me | solution 1 for GRH.centered_moebius_square_block_control
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:24:15.443169+00:00
-- url     : https://prove2.me/submissions/7a7cb0d4-0f56-4491-a175-c147a6552b69

import Definitions.Def_GRH_MoebiusBilinear
import Theorems.Thm_GRH_reduced_harmonic_cancellation_above_verified_boundary
import Theorems.Thm_GRH_liouville_reduced_progression_bound_above_record
import Theorems.Thm_GRH_moebius_progression_le_of_liouville_progression_le
import Mathlib

/- The finite Mobius inversion and centering lemmas below adapt public Prove2Me
submissions 509e229b and 0176d409. Both are independent of their open children. -/
/-!
The coefficient identity follows Helfgott–Thompson, §2, (2.1), doi:10.1007/s40993-022-00408-8.
The weighted divisor-pair argument adapts the reindexing in Mathlib's
ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (ArithmeticFunction/Misc.lean, Apache 2.0,
copyright 2020 Aaron Anderson). Only the final declaration uses the proposed child.
-/

open scoped BigOperators
open Finset

namespace MobiusProgression

abbrev mu : ArithmeticFunction ℝ := ArithmeticFunction.moebius
abbrev zeta : ArithmeticFunction ℝ := ArithmeticFunction.zeta

noncomputable def short (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k ≤ u then (ArithmeticFunction.moebius k : ℝ) else 0, by simp⟩

-- Two factors above the square-root cutoff cannot have product at most n.
private theorem tail_square_zero (n k : ℕ) (hk : k ≤ n) :
    ((mu - short n.sqrt) * (mu - short n.sqrt)) k = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hsmall : p.1 ≤ n.sqrt ∨ p.2 ≤ n.sqrt := by
    by_contra! h
    have hh := Nat.mul_le_mul h.1 h.2
    have hn := Nat.lt_succ_sqrt n
    omega
  change ((ArithmeticFunction.moebius p.1 : ℝ) - (if p.1 ≤ n.sqrt then _ else 0)) *
      ((ArithmeticFunction.moebius p.2 : ℝ) - (if p.2 ≤ n.sqrt then _ else 0)) = 0
  rcases hsmall with h | h <;> simp [h]

theorem truncated_coefficient (n k : ℕ) (hk : k ≤ n) :
    mu k = short n.sqrt k + short n.sqrt k - (short n.sqrt * (short n.sqrt * zeta)) k := by
  let s := short n.sqrt
  have hinv : mu * zeta = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have halg : (mu - s) * (mu - s) * zeta = mu - s - s + s * (s * zeta) := by
    calc
      _ = mu * (mu * zeta) - s * (mu * zeta) - s * (mu * zeta) + s * (s * zeta) := by ring
      _ = _ := by rw [hinv]; simp
  have hzero : ((mu - s) * (mu - s) * zeta) k = 0 := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    refine sum_eq_zero fun d hd => tail_square_zero n d ?_
    obtain ⟨hdvd,hk0⟩ := Nat.mem_divisors.mp hd
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd).trans hk
  rw [halg] at hzero
  change mu k - s k - s k + (s * (s * zeta)) k = 0 at hzero
  change mu k = s k + s k - (s * (s * zeta)) k
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
    (∑ k ∈ Ioc 0 N, short u k * F k) = ∑ k ∈ Ioc 0 u, mu k * F k := by
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
      simp [short, (mem_Ioc.mp hk).2, mu]

noncomputable def residueWeight {q : ℕ} (a : ZMod q) (k : ℕ) : ℝ :=
  if (k : ZMod q) = a then 1 else 0

noncomputable def bilinear {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n.sqrt, mu d * ∑ e ∈ Ioc 0 n.sqrt, mu e *
    (((Ioc 0 (n / (d * e))).filter (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

theorem reindex_bilinear {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ Ioc 0 n, residueWeight a k * (short n.sqrt * (short n.sqrt * zeta)) k) =
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
  have hr0 := (mem_Ioc.mp hr).1.ne'
  simp [residueWeight, zeta, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hr0, Nat.mul_assoc]

noncomputable def partialSum {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 n, mu k * residueWeight a k

theorem weighted_identity {q : ℕ} (a : ZMod q) (n : ℕ) :
    partialSum a n = 2 * partialSum a n.sqrt - bilinear a n := by
  unfold partialSum
  rw [← reindex_bilinear, ← truncate_sum n _ (Nat.sqrt_le_self n)]
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [truncated_coefficient n k (mem_Ioc.mp hk).2]
  ring

private theorem parent_sum {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) = partialSum a n := by
  classical
  have hr : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hr, sum_insert (by simp)]
  have hz : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by simp
  simp only [hz, ite_self, zero_add]
  refine sum_congr rfl fun k _ => ?_
  simp only [residueWeight, mu, ArithmeticFunction.intCoe_apply]
  split_ifs <;> simp_all

private theorem partialSum_abs_le {q : ℕ} (a : ZMod q) (u : ℕ) :
    |partialSum a u| ≤ (u : ℝ) := by
  unfold partialSum
  calc
    _ ≤ ∑ k ∈ Ioc 0 u, |mu k * residueWeight a k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Ioc 0 u, (1 : ℝ) := by
      refine sum_le_sum fun k _ => ?_
      have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
      by_cases h : (k : ZMod q) = a <;> simp [residueWeight, h, mu, hmu]
    _ = _ := by simp

theorem short_bound {q : ℕ} (a : ZMod q) (n : ℕ) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) ≤ σ) : |partialSum a n.sqrt| ≤ ((n : ℝ) + 1) ^ σ := by
  calc
    _ ≤ (n.sqrt : ℝ) := partialSum_abs_le a n.sqrt
    _ ≤ Real.sqrt ((n : ℝ) + 1) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have h : (n.sqrt : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
      linarith
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by simp) hhalf

end MobiusProgression

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


theorem GRH.moebius_bilinear_eq_centered
    (q : ℕ) [NeZero q] (a : ZMod q) (N : ℕ) :
    (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius e : ℝ) *
        (((Finset.Ioc 0 (N / (d * e))).filter
          (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)) =
      GRH.centeredMoebiusBilinear q a N +
        (1 / (q : ℝ)) * (N : ℝ) *
          (GRH.reducedMoebiusHarmonic q N.sqrt) ^ 2 := by
  classical
  let h : ℕ → ℝ := fun d => if IsUnit (d : ZMod q) then 1 / (d : ℝ) else 0
  have harmonic :
      (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) * h d) =
        GRH.reducedMoebiusHarmonic q N.sqrt := by
    unfold GRH.reducedMoebiusHarmonic
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hu : IsUnit (d : ZMod q) <;> simp [h, hu, div_eq_mul_inv]
  have kernel (d e : ℕ) :
      (if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        (1 / (q : ℝ)) * (N : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
      ((1 / (q : ℝ)) * (N : ℝ)) * h d * h e := by
    by_cases hd : IsUnit (d : ZMod q) <;> by_cases he : IsUnit (e : ZMod q) <;>
      simp [h, hd, he, div_eq_mul_inv, mul_inv_rev] <;> ring
  change (∑ d ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius d : ℝ) *
      ∑ e ∈ Finset.Ioc 0 N.sqrt, (ArithmeticFunction.moebius e : ℝ) *
        GRH.moebiusProgressionCount q a N d e) = _
  unfold GRH.centeredMoebiusBilinear
  simp_rw [kernel]
  rw [← harmonic]
  exact centered_sum (Finset.Ioc 0 N.sqrt)
    (fun d => (ArithmeticFunction.moebius d : ℝ)) h
    (GRH.moebiusProgressionCount q a N) ((1 / (q : ℝ)) * (N : ℝ))


open GRH

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



open Filter Asymptotics MobiusProgression
open GRH

private theorem centered_formula {q : ℕ} [NeZero q] (a : ZMod q) (N : ℕ) :
    centeredMoebiusBilinear q a N = 2*partialSum a N.sqrt - partialSum a N -
      (1/(q:ℝ))*N*(reducedMoebiusHarmonic q N.sqrt)^2 := by
  have h := weighted_identity a N
  have h' : bilinear a N = centeredMoebiusBilinear q a N +
      (1/(q:ℝ))*N*(reducedMoebiusHarmonic q N.sqrt)^2 := moebius_bilinear_eq_centered q a N
  linarith only [h,h']

private theorem progression_increment {q : ℕ} (a : ZMod q) (N h : ℕ) :
    |partialSum a (N+h)-partialSum a N| ≤ (h:ℝ) := by
  unfold partialSum
  have hu := Finset.Ioc_union_Ioc_eq_Ioc (a:=0) (b:=N) (c:=N+h) (by omega) (by omega)
  rw [←hu,Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),add_sub_cancel_left]
  calc _ ≤ ∑ k ∈ Ioc N (N+h), |mu k * residueWeight a k| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ _k ∈ Ioc N (N+h), (1:ℝ) := by
          apply sum_le_sum
          intro k _
          have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
          by_cases hz : (k : ZMod q) = a <;> simp [residueWeight,hz,mu,hmu]
       _ = _ := by simp

private theorem block_variation (q : ℕ) [NeZero q] (a : ZMod q) (u j : ℕ) (hj : j ≤ 2*u) :
    |centeredMoebiusBilinear q a (u^2+j)-centeredMoebiusBilinear q a (u^2)| ≤
      (j:ℝ)*(1+(1/(q:ℝ))*(reducedMoebiusHarmonic q u)^2) := by
  have he := Nat.sqrt_add_eq' u (by omega : j ≤ u+u)
  rw [centered_formula a,centered_formula a,Nat.sqrt_eq',he]
  push_cast
  rw [show 2*partialSum a u-partialSum a (u^2+j)-1/(q:ℝ)*((u:ℝ)^2+j)*reducedMoebiusHarmonic q u^2 -
      (2*partialSum a u-partialSum a (u^2)-1/(q:ℝ)*(u:ℝ)^2*reducedMoebiusHarmonic q u^2) =
      -(partialSum a (u^2+j)-partialSum a (u^2)) - ((j:ℝ)*(1/q)*(reducedMoebiusHarmonic q u)^2) by ring]
  apply (abs_sub _ _).trans
  rw [abs_neg,abs_of_nonneg (by positivity : 0 ≤ (j:ℝ)*(1/q)*(reducedMoebiusHarmonic q u)^2)]
  linarith only [progression_increment a (u^2) j]

private theorem block_harmonic_bound (q : ℕ) [NeZero q] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ, |reducedMoebiusHarmonic q u| ≤ C := by
  obtain ⟨C,hC,h⟩ := reduced_harmonic_cancellation_above_verified_boundary q (9/10) (by norm_num) (by norm_num)
  refine ⟨C,hC,fun u => ?_⟩
  have hp : ((u:ℝ)+1)^(9/10-1:ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α:=ℝ) u]) (by norm_num)
  exact ((le_max_right ..).trans (h u)).trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (mul_one C))

private theorem block_mean_control (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, let u := N.sqrt
      |centeredMoebiusBilinear q a N - (∑ j ∈ range (2*u+1), centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)| ≤
        K*(u+1:ℝ) := by
  obtain ⟨C,hC,h⟩ := block_harmonic_bound q
  let c := 1+(1/(q:ℝ))*C^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨4*c,by positivity,fun N => ?_⟩
  let u := N.sqrt
  let f := centeredMoebiusBilinear q a
  have hu : u^2 ≤ N := Nat.sqrt_le' N
  have hub : N ≤ u^2 + 2*u := by simpa [u,pow_two,two_mul,add_assoc] using Nat.sqrt_le_add N
  have hv (j : ℕ) (hj : j ≤ 2*u) : |f (u^2+j)-f (u^2)| ≤ (2*(u:ℝ))*c := by
    apply (block_variation q a u j hj).trans
    apply mul_le_mul _ _ (by positivity) (by positivity)
    · exact_mod_cast hj
    · dsimp only [c]
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (h u)
  have hN := hv (N-u^2) (by omega)
  rw [Nat.add_sub_of_le hu] at hN
  let m := 2*u+1
  have hm : (0:ℝ) < m := by dsimp [m]; positivity
  have hd (j : ℕ) (hj : j ∈ range m) : |f N-f (u^2+j)| ≤ 4*(u:ℝ)*c := by
    have h1 := (abs_sub_le (f N) (f (u^2)) (f (u^2+j)))
    rw [abs_sub_comm (f (u^2))] at h1
    have h2 := hv j (by have hh := mem_range.mp hj; dsimp [m] at hh; omega)
    linarith only [h1,h2,hN]
  change |f N - (∑ j ∈ range m, f (u^2+j))/(m:ℝ)| ≤ _
  have heq : f N - (∑ j ∈ range m, f (u^2+j))/(m:ℝ) =
      (∑ j ∈ range m, (f N - f (u^2+j)))/(m:ℝ) := by
    rw [sum_sub_distrib]; simp only [sum_const,card_range,nsmul_eq_mul];field_simp
  rw [heq,abs_div,abs_of_pos hm]
  apply (div_le_iff₀ hm).2
  calc _ ≤ ∑ j ∈ range m, |f N-f (u^2+j)| := abs_sum_le_sum_abs _ _
       _ ≤ ∑ _j ∈ range m, 4*(u:ℝ)*c := sum_le_sum hd
       _ ≤ _ := by simp only [sum_const,card_range,nsmul_eq_mul]; dsimp [u]; nlinarith [mul_nonneg hm.le hc]

private theorem centered_above_record (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hσ : 0.8749570698 < σ) (hs : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |centeredMoebiusBilinear q a n| ≤ C*((n:ℝ)+1)^σ := by
  have hhalf : (1/2:ℝ) < σ := by linarith
  obtain ⟨A,hA,hL⟩ := liouville_reduced_progression_bound_above_record q σ hσ
  let B := A*(2:ℝ)^σ*(∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hM (n : ℕ) : |partialSum a n| ≤ B*((n:ℝ)+1)^σ := by
    rw [←MobiusProgression.parent_sum]
    exact moebius_progression_le_of_liouville_progression_le q σ A hhalf hA hL a ha n
  obtain ⟨K,hK,hboth⟩ := reduced_harmonic_cancellation_above_verified_boundary q σ hσ hs
  let V := (1/(q:ℝ))*K^2
  have hV : 0 ≤ V := by dsimp [V]; positivity
  refine ⟨2+B+V,by positivity,fun n => ?_⟩
  let X := ((n:ℝ)+1)^σ
  have hsmall := MobiusProgression.short_bound a n σ hhalf.le
  have hmain := harmonic_main_weight_bound n σ K (reducedMoebiusHarmonic q n.sqrt) hs hK
    ((le_max_right ..).trans (hboth n.sqrt))
  have hmain' : |(1/(q:ℝ))*(n:ℝ)*(reducedMoebiusHarmonic q n.sqrt)^2| ≤ V*X := by
    rw [abs_of_nonneg (by positivity),mul_assoc]; dsimp [V,X]; rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmain (by positivity)
  rw [centered_formula]
  calc _ ≤ |2*partialSum a n.sqrt-partialSum a n|+|(1/(q:ℝ))*(n:ℝ)*(reducedMoebiusHarmonic q n.sqrt)^2| := abs_sub ..
       _ ≤ (|2*partialSum a n.sqrt|+|partialSum a n|)+V*X := add_le_add (abs_sub ..) hmain'
       _ ≤ (2*X+B*X)+V*X := by
          rw [abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
          exact add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0:ℝ)≤2)) (hM n)) _
       _ = _ := by dsimp [X];ring

theorem solution (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, let u := N.sqrt
      |centeredMoebiusBilinear q a N -
        (∑ j ∈ range (2*u+1), centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)| ≤ K*((u:ℝ)+1)) ∧
    (∀ σ : ℝ, 0.8749570698 < σ → σ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |centeredMoebiusBilinear q a n| ≤ C*((n:ℝ)+1)^σ) := by
  exact ⟨block_mean_control q a,fun σ hσ hs => centered_above_record q a ha σ hσ hs⟩

