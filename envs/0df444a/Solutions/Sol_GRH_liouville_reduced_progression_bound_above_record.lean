-- Prove2me | solution 1 for GRH.liouville_reduced_progression_bound_above_record
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:37:17.83377+00:00
-- url     : https://prove2.me/submissions/9558ab77-0a95-4b94-a6c3-d40f7dce4699

import Theorems.Thm_GRH_mobius_character_and_progression_bounds_above_record
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic

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

private theorem reduced_classes_uniform_real (q : ℕ) [NeZero q] (σ : ℝ) (hσ : 0 ≤ σ)
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

theorem solution (q : ℕ) [NeZero q] (σ : ℝ) (hσ : (0.8749570698:ℝ) < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then (liouville j:ℝ) else 0| ≤ C*((N:ℝ)+1)^σ := by
  have hhalf : 1/2 < σ := by linarith
  have hpos : 0 ≤ σ := by linarith
  obtain ⟨C,hC,hM⟩ := reduced_classes_uniform_real q σ hpos moebius
    (GRH.mobius_character_and_progression_bounds_above_record q σ hσ).2
  refine ⟨C * (2:ℝ)^σ * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹, by positivity, ?_⟩
  intro a ha N
  rw [GRH.liouville_progression_square_sieve]
  exact GRH.square_divisor_progression_bound (fun k : ℕ => (moebius k : ℝ))
    (by simp) q σ C hhalf hC hM a ha N
