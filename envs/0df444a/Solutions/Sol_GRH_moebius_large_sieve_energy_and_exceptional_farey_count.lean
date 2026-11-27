-- Prove2me | solution 1 for GRH.moebius_large_sieve_energy_and_exceptional_farey_count
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T05:25:00.651556+00:00
-- url     : https://prove2.me/submissions/365f47be-8496-474e-89c4-fe5124c4b0cc

import Theorems.Thm_GRH_centered_bilinear_additive_modes_and_residue_inversion
import Theorems.Thm_LargeSieve_analytic_large_sieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Finset GRH.AdditiveMoebiusSpectrum

private theorem fareyDistance {Q : ℕ} (hQ : 2 ≤ Q) {x y : ℚ}
    (hx : 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q) (hy : 0 ≤ y ∧ y < 1 ∧ y.den ≤ Q)
    (hne : x ≠ y) (k : ℤ) : 1/(Q : ℝ)^2 ≤ |(x : ℝ) - (y : ℝ) - k| := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx.1
  have hy0 : (0 : ℝ) ≤ y := by exact_mod_cast hy.1
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast hx.2.1
  have hy1 : (y : ℝ) < 1 := by exact_mod_cast hy.2.1
  have he : (x : ℝ)-(y : ℝ)-(k : ℝ) ≠ 0 := by
    intro e
    have lk : (-1 : ℤ) < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
    have uk : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by linarith)
    have z : k=0 := by omega
    subst k
    have eq : (x : ℝ)=(y : ℝ) := by norm_num at e; linarith
    exact hne (by exact_mod_cast eq)
  let v : ℤ := x.num*y.den - y.num*x.den - k*x.den*y.den
  let d : ℝ := (x.den : ℝ)*y.den
  have hxden : (0 : ℝ) < x.den := by exact_mod_cast x.den_pos
  have hyden : (0 : ℝ) < y.den := by exact_mod_cast y.den_pos
  have hd : 0 < d := mul_pos hxden hyden
  have hw : ((x : ℝ)-(y : ℝ)-(k : ℝ))*d = v := by
    dsimp [d,v]
    rw [Rat.cast_def x,Rat.cast_def y]
    push_cast
    field_simp
  have hv : v ≠ 0 := by
    intro h
    have h' : ((x : ℝ)-(y : ℝ)-(k : ℝ))*d = 0 := by rw [hw,h,Int.cast_zero]
    exact (mul_ne_zero he hd.ne') h'
  have hab : (1 : ℤ) ≤ |v| := by
    have := abs_pos.mpr hv
    omega
  have hval : (1 : ℝ) ≤ |(x : ℝ)-(y : ℝ)-k| * d := by
    rw [← abs_of_pos hd,← abs_mul,hw]
    exact_mod_cast hab
  have hQ' : 0 < (Q : ℝ)^2 := by
    have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
    positivity
  have hdQ : d ≤ (Q : ℝ)^2 := by
    rw [pow_two]
    exact mul_le_mul (by exact_mod_cast hx.2.2) (by exact_mod_cast hy.2.2)
      hyden.le (Nat.cast_nonneg Q)
  exact (div_le_iff₀ hQ').2 (hval.trans (mul_le_mul_of_nonneg_left hdQ (abs_nonneg _)))

private theorem countEnergy (s : Bool) (N : ℕ) :
    ∑ n ∈ range (N+1), ‖(weight s N n : ℂ)‖^2 ≤ (N : ℝ) := by
  have one (k : ℕ) : ‖(weight s N k : ℂ)‖ ≤ 1 := by
    have h : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=k))
    rw [Complex.norm_real,Real.norm_eq_abs]
    unfold weight
    split_ifs <;> simpa using h
  rw [sum_range_succ']
  have z : (weight s N 0 : ℂ) = 0 := by simp [weight]
  simp only [z,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,add_zero]
  calc
    _ ≤ ∑ _k ∈ range N, (1 : ℝ)^2 :=
      sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (one (k+1)) _
    _ = _ := by simp

private theorem frequencyBounds (s : Bool) (Q N : ℕ) (hQ : 2 ≤ Q) (A : Finset ℚ)
    (hA : ∀ x ∈ A, 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q) :
    (∑ x ∈ A, ‖transform s N x‖^2) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N ∧
    (∀ T : ℝ, 0 ≤ T → ((exceptional s N A T).card : ℝ)*T^2 ≤
      ((Q : ℝ)^2+13*((N : ℝ)+1))*N) := by
  classical
  let e := (Fintype.equivFin (↥A)).symm
  let α := fun i => ((e i).val : ℝ)
  have sep : ∀ i j, i ≠ j → 1/(Q : ℝ)^2 ≤ |α i-α j-round (α i-α j)| := by
    intro i j ne
    exact fareyDistance hQ (hA _ (e i).property) (hA _ (e j).property)
      (fun h => ne (e.injective (Subtype.ext h))) _
  have q2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have qp : 0 < (Q : ℝ)^2 := by positivity
  have d2 : 1/(Q : ℝ)^2 ≤ 1/2 := (div_le_iff₀ qp).mpr (by nlinarith [sq_nonneg ((Q : ℝ)-2)])
  have sieve := LargeSieve.analytic_large_sieve (N:=N+1) (fun k => (weight s N k : ℂ))
    sep (by positivity) d2
  have reindex : (∑ x ∈ A, ‖transform s N x‖^2) =
      ∑ i, ‖transform s N (e i).val‖^2 := by
    calc
      _ = ∑ x : ↥A, ‖transform s N x.val‖^2 := by
        rw [← A.sum_attach (fun x => ‖transform s N x‖^2),attach_eq_univ]
      _ = _ := (Equiv.sum_comp e (fun x : ↥A => ‖transform s N x.val‖^2)).symm
  have en : (∑ x ∈ A, ‖transform s N x‖^2) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N := by
    rw [reindex]
    simp only [one_div,inv_inv,Nat.cast_add,Nat.cast_one] at sieve
    exact sieve.trans (mul_le_mul_of_nonneg_left (countEnergy s N) (by positivity))
  refine ⟨en,?_⟩
  intro T hT
  calc
    _ = ∑ _x ∈ exceptional s N A T, T^2 := by simp
    _ ≤ ∑ x ∈ exceptional s N A T, ‖transform s N x‖^2 := by
      apply sum_le_sum
      intro x hx
      exact pow_le_pow_left₀ hT (mem_filter.mp hx).2.le _
    _ ≤ ∑ x ∈ A, ‖transform s N x‖^2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ _ := en

private noncomputable def primeAngles (p : Nat.Primes) : Finset ℚ :=
  haveI : NeZero p.val := ⟨p.property.ne_zero⟩
  ((univ : Finset (ZMod p.val)).erase 0).image angle

private theorem angleInj {q : ℕ} [NeZero q] : Function.Injective (@angle q) := by
  intro a b eq
  unfold angle at eq
  have hq : (q : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ev := (div_left_inj' hq).mp eq
  exact ZMod.val_injective q (by exact_mod_cast ev)

private theorem primeDen (p : Nat.Primes) (h : ZMod p.val) (hn : h ≠ 0) :
    (angle h).den = p.val := by
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  have hv : 0 < h.val := Nat.pos_of_ne_zero fun e => hn ((ZMod.val_eq_zero h).mp e)
  have hc : Nat.Coprime h.val p.val := (p.property.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hv (ZMod.val_lt h))).symm
  have H := Rat.den_div_eq_of_coprime (a:=(h.val : ℤ)) (b:=(p.val : ℤ))
    (by exact_mod_cast p.property.pos) (by simpa only [Int.natAbs_natCast] using hc)
  unfold angle
  simp only [Int.cast_natCast] at H
  exact Int.ofNat.inj H

private theorem primeAngleBounds (p : Nat.Primes) {x : ℚ} (hx : x ∈ primeAngles p) :
    0 ≤ x ∧ x < 1 ∧ x.den=p.val := by
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  obtain ⟨h,hh,rfl⟩ := mem_image.mp hx
  have hp : (0 : ℚ) < p.val := by exact_mod_cast p.property.pos
  exact ⟨div_nonneg (Nat.cast_nonneg _) hp.le,(div_lt_one hp).2 (by exact_mod_cast ZMod.val_lt h),
    primeDen p h (mem_erase.mp hh).1⟩

private theorem primeEnergy (Q N : ℕ) (hQ : 2 ≤ Q) (P : Finset Nat.Primes)
    (hp : ∀ p ∈ P, p.val ≤ Q) :
    (∑ p ∈ P, (p.val : ℝ)*primeVariance p N) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N := by
  classical
  have iden (p : Nat.Primes) : (p.val : ℝ)*primeVariance p N =
      ∑ x ∈ primeAngles p, ‖transform true N x‖^2 := by
    let : NeZero p.val := ⟨p.property.ne_zero⟩
    unfold primeAngles
    rw [sum_image (fun _ _ _ _ eq => angleInj eq)]
    exact (GRH.centered_bilinear_additive_modes_and_residue_inversion p.val N).2.2
  have hd : (P : Set Nat.Primes).PairwiseDisjoint primeAngles := by
    intro p _ r _ hpr
    apply disjoint_left.mpr
    intro x hx hy
    exact hpr (Subtype.ext ((primeAngleBounds p hx).2.2.symm.trans (primeAngleBounds r hy).2.2))
  let A := P.biUnion primeAngles
  have hA (x : ℚ) (hx : x ∈ A) : 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q := by
    obtain ⟨p,hp',hx'⟩ := mem_biUnion.mp hx
    obtain ⟨hx0,hx1,hd⟩ := primeAngleBounds p hx'
    exact ⟨hx0,hx1,hd.le.trans (hp p hp')⟩
  calc
    _ = ∑ p ∈ P, ∑ x ∈ primeAngles p, ‖transform true N x‖^2 := sum_congr rfl fun p _ => iden p
    _ = ∑ x ∈ A, ‖transform true N x‖^2 := (sum_biUnion hd).symm
    _ ≤ _ := (frequencyBounds true Q N hQ A hA).1

theorem solution (Q N : ℕ) (hQ : 2 ≤ Q) :
    (∀ (s : Bool) (A : Finset ℚ), (∀ x ∈ A, 0 ≤ x ∧ x < 1 ∧ x.den ≤ Q) →
      (∑ x ∈ A, ‖transform s N x‖^2) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N ∧
      (∀ T : ℝ, 0 ≤ T → ((exceptional s N A T).card : ℝ)*T^2 ≤
        ((Q : ℝ)^2+13*((N : ℝ)+1))*N)) ∧
    (∀ P : Finset Nat.Primes, (∀ p ∈ P, p.val ≤ Q) →
      (∑ p ∈ P, (p.val : ℝ)*primeVariance p N) ≤ ((Q : ℝ)^2+13*((N : ℝ)+1))*N) := by
  exact ⟨fun s A => frequencyBounds s Q N hQ A,primeEnergy Q N hQ⟩
