-- Prove2me | solution 1 for GRH.liouville_reduced_progression_bound_below_record
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pragyan
-- created : 2026-11-21T03:59:36.472179+00:00
-- url     : https://prove2.me/submissions/5cab841d-8160-4d50-9bed-a033cbeea467
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_moebius_reduced_progression_bilinear_power_bound

/-!
Finite Möbius truncation adapted from meadowlark's Apache-2.0 Prove2Me
submission 509e229b-7ae5-4fe8-b643-d32c7895621a. It follows Helfgott–Thompson,
§2, equations (2.1)–(2.2), doi:10.1007/s40993-022-00408-8. The weighted
reindexing follows Mathlib ArithmeticFunction/Misc.lean, Apache 2.0,
copyright 2020 Aaron Anderson. No partial-sum ancestor is imported.
-/
set_option autoImplicit false
open scoped BigOperators
open Finset ArithmeticFunction Filter Asymptotics

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

theorem reduction {q : ℕ} (a : ZMod q) (σ : ℝ) (hhalf : (1 / 2 : ℝ) ≤ σ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |bilinear a n| ≤ C * ((n : ℝ) + 1) ^ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ range (n + 1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0|
        ≤ C * ((n : ℝ) + 1) ^ σ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2 + C, by positivity, fun n => ?_⟩
  rw [parent_sum, weighted_identity]
  calc
    _ ≤ |2 * partialSum a n.sqrt| + |bilinear a n| := abs_sub _ _
    _ = 2 * |partialSum a n.sqrt| + |bilinear a n| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (((n : ℝ) + 1) ^ σ) + C * ((n : ℝ) + 1) ^ σ :=
      add_le_add (mul_le_mul_of_nonneg_left (short_bound a n σ hhalf) (by norm_num)) (h n)
    _ = _ := by ring

end MobiusProgression

/- Square-divisor identities reused from the accepted proof of GRH.uniform_mobius_liouville_progressions_of_zero_free. -/
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



open scoped BigOperators
open Finset


theorem solution
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1)
    (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ Finset.range (N + 1), if (j : ZMod q) = a then (ArithmeticFunction.liouville j : ℝ) else 0| ≤
        C * ((N : ℝ) + 1) ^ σ := by
  classical
  have hclasses : ∀ a : ZMod q, ∃ C : ℝ, 0 ≤ C ∧ (IsUnit a → ∀ N : ℕ,
      |∑ k ∈ range (N+1), if (k : ZMod q) = a then (moebius k : ℝ) else 0| ≤
        C * ((N : ℝ)+1)^σ) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨C,hC,hB⟩ := MobiusProgression.reduction a σ hhalf.le
        (GRH.moebius_reduced_progression_bilinear_power_bound q a ha σ hhalf hone)
      exact ⟨C,hC,fun _ => hB⟩
    · exact ⟨0,le_rfl,fun h => (ha h).elim⟩
  choose C hC hclasses using hclasses
  let M : ℝ := ∑ a : ZMod q, C a
  have hM : 0 ≤ M := Finset.sum_nonneg (fun a _ => hC a)
  have hMb : ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ k ∈ range (N+1), if (k : ZMod q) = a then (moebius k : ℝ) else 0| ≤
        M * ((N : ℝ)+1)^σ := by
    intro a ha N
    apply (hclasses a ha N).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ a)
  let L : ℝ := M * (2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  have hL : 0 ≤ L := by
    dsimp [L]
    apply mul_nonneg (mul_nonneg hM (by positivity))
    exact tsum_nonneg (fun d => by positivity)
  refine ⟨L, hL, ?_⟩
  intro a ha N
  rw [GRH.liouville_progression_square_sieve]
  exact GRH.square_divisor_progression_bound (fun k => (moebius k : ℝ)) (by simp)
    q σ M hhalf hM hMb a ha N
