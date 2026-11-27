-- Prove2me | solution 1 for GRH.prime_square_fourier_filter_and_coprime_harmonic_recursion
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:04:04.442753+00:00
-- url     : https://prove2.me/submissions/ee3f3cdf-1dd7-484d-9427-d6451ad0a244

import Definitions.Def_GRH_SquarefullFrequencies
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

private theorem sumMultiples {R : Type*} [AddCommMonoid R] (p N : ℕ) (hp : 0 < p) (f : ℕ → R) :
    (∑ k ∈ (range (N+1)).filter (fun k => p ∣ k), f k) =
      ∑ k ∈ range (N/p+1), f (p*k) := by
  refine sum_nbij' (i:=fun k => k/p) (j:=fun k => p*k) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      (Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1))))
  · intro k hk
    have h := (Nat.le_div_iff_mul_le hp).mp (Nat.lt_succ_iff.mp (mem_range.mp hk))
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (by simpa only [mul_comm] using h)),
      dvd_mul_right ..⟩
  · intro k hk
    exact Nat.mul_div_cancel' (mem_filter.mp hk).2
  · intro k _
    exact Nat.mul_div_cancel_left k hp
  · intro k hk
    rw [Nat.mul_div_cancel' (mem_filter.mp hk).2]

private theorem primeMu (p n : ℕ) (hp : p.Prime) :
    ArithmeticFunction.moebius (p*n) = if p ∣ n then 0 else -ArithmeticFunction.moebius n := by
  by_cases h : p ∣ n
  · rw [if_pos h]
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hs
    exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (Nat.mul_dvd_mul_left p h)
  · rw [if_neg h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (hp.coprime_iff_not_dvd.mpr h), ArithmeticFunction.moebius_apply_prime hp,neg_one_mul]

private theorem phaseAdd (n : ℕ) (x y : ℚ) : phase n (x+y) = phase n x * phase n y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phaseRational (n j d : ℕ) [NeZero d] :
    phase n ((j : ℚ)/d) = ZMod.stdAddChar ((n : ZMod d)*(j : ZMod d)) := by
  have he := ZMod.stdAddChar_coe (N:=d) ((n*j : ℕ) : ℤ)
  push_cast at he
  rw [he]
  unfold phase
  push_cast
  congr 1
  ring

private theorem completePhases (d n : ℕ) [NeZero d] :
    ∑ j ∈ range d, phase n ((j : ℚ)/d) = if d ∣ n then (d : ℂ) else 0 := by
  classical
  have index (f : ZMod d → ℂ) : ∑ j ∈ range d, f (j : ZMod d) = ∑ b : ZMod d, f b := by
    exact sum_nbij' (i:=fun j => ((j : ℕ) : ZMod d)) (j:=fun b => b.val)
      (fun _ _ => mem_univ _) (fun b _ => mem_range.mpr (ZMod.val_lt b))
      (fun _ hj => ZMod.val_natCast_of_lt (mem_range.mp hj))
      (fun b _ => ZMod.natCast_rightInverse b) (fun _ _ => rfl)
  simp_rw [phaseRational]
  rw [index (fun b => ZMod.stdAddChar ((n : ZMod d)*b))]
  by_cases h : d ∣ n
  · have hn := (ZMod.natCast_eq_zero_iff n d).mpr h
    simp [h,hn,ZMod.card]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d
      (fun e => h ((ZMod.natCast_eq_zero_iff n d).mp e)))

private theorem raw (N : ℕ) (x : ℚ) :
    transform false N x = ∑ n ∈ range (N+1), (ArithmeticFunction.moebius n : ℂ)*phase n x := by
  simp [transform,weight,phase]

private noncomputable def multiplePart (d N : ℕ) (x : ℚ) : ℂ :=
  ∑ n ∈ (range (N+1)).filter (fun n => d ∣ n), (ArithmeticFunction.moebius n : ℂ)*phase n x

private theorem shiftFilter (d N : ℕ) [NeZero d] (x : ℚ) :
    shifts d N x = (d : ℂ)*multiplePart d N x := by
  classical
  unfold shifts
  simp_rw [raw,phaseAdd,← mul_assoc]
  rw [sum_comm]
  simp_rw [← mul_sum,completePhases]
  unfold multiplePart
  rw [mul_sum,sum_filter]
  apply sum_congr rfl
  intro n _
  split_ifs <;> ring

private theorem multiplesModSquare (p : ℕ) (hp : p.Prime) (N : ℕ) (x : ℚ) :
    (∑ j ∈ (range (p^2)).filter (fun j => p ∣ j),
        transform false N (x + (j : ℚ)/(p : ℚ)^2)) = shifts p N x := by
  unfold shifts
  apply sum_nbij' (i:=fun j => j/p) (j:=fun j => p*j)
  · intro j hj
    exact mem_range.mpr ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by
      simpa [pow_two] using mem_range.mp (mem_filter.mp hj).1))
  · intro j hj
    exact mem_filter.mpr ⟨mem_range.mpr (by
      simpa only [pow_two] using ((Nat.mul_lt_mul_left hp.pos).mpr (mem_range.mp hj))),dvd_mul_right ..⟩
  · intro j hj
    exact Nat.mul_div_cancel' (mem_filter.mp hj).2
  · intro j _
    exact Nat.mul_div_cancel_left j hp.pos
  · intro j hj
    obtain ⟨k,rfl⟩ := (mem_filter.mp hj).2
    rw [Nat.mul_div_cancel_left _ hp.pos]
    congr 2
    push_cast
    have h : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp

private theorem squareShifts (p N : ℕ) [NeZero p] (hp : p.Prime) (x : ℚ) :
    primeSquareShifts p N x = -(p : ℂ)*multiplePart p N x := by
  classical
  have z : shifts (p^2) N x = 0 := by
    rw [shiftFilter]
    have e : multiplePart (p^2) N x = 0 := by
      unfold multiplePart
      apply sum_eq_zero
      intro n hn
      have h := (mem_filter.mp hn).2
      have hh : ArithmeticFunction.moebius n = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree
          (fun sf => (Nat.squarefree_iff_prime_squarefree.mp sf p hp) (by simpa [pow_two] using h))
      simp only [hh,Int.cast_zero,zero_mul]
    rw [e,mul_zero]
  have h := sum_filter_add_sum_filter_not (range (p^2)) (fun j => p ∣ j)
    (fun j => transform false N (x + (j : ℚ)/(p : ℚ)^2))
  rw [multiplesModSquare p hp N x,shiftFilter] at h
  change _ + primeSquareShifts p N x = _ at h
  have eq : (∑ j ∈ range (p^2), transform false N (x+(j : ℚ)/(p : ℚ)^2)) = 0 := by
    simpa only [shifts,Nat.cast_pow] using z
  rw [eq] at h
  linear_combination h

private theorem liftMultiples (p N : ℕ) [NeZero p] (hp : p.Prime) (x : ℚ) :
    multiplePart p (p*N) (x/p) = multiplePart p N x - transform false N x := by
  classical
  unfold multiplePart
  rw [sumMultiples p (p*N) hp.pos,Nat.mul_div_cancel_left _ hp.pos,raw,sum_filter,← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  have ep : phase (p*k) (x/p) = phase k x := by
    unfold phase
    congr 1
    push_cast
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp
  rw [ep,primeMu p k hp]
  by_cases h : p ∣ k <;> simp [h]

private theorem harmonic (p U : ℕ) [NeZero p] (hp : p.Prime) :
    GRH.reducedMoebiusHarmonic p U = GRH.reducedMoebiusHarmonic 1 U +
      GRH.reducedMoebiusHarmonic p (U/p)/(p : ℝ) := by
  classical
  let f := fun k : ℕ => (ArithmeticFunction.moebius k : ℝ)/(k : ℝ)
  have hzero : f 0=0 := by simp [f]
  have pref (d V : ℕ) [NeZero d] :
      GRH.reducedMoebiusHarmonic d V =
      ∑ n ∈ range (V+1), if IsUnit (n : ZMod d) then f n else 0 := by
    have rr : range (V+1)=insert 0 (Ioc 0 V) := by ext n; simp
    rw [rr,sum_insert (by simp)]
    simp [GRH.reducedMoebiusHarmonic,hzero,f]
  have unitp (n : ℕ) : IsUnit (n : ZMod p) ↔ ¬p ∣ n := by
    rw [ZMod.isUnit_iff_coprime,Nat.coprime_comm,hp.coprime_iff_not_dvd]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have ev (k : ℕ) : f (p*k) = -(if ¬p ∣ k then f k else 0)/(p : ℝ) := by
    rw [show f (p*k)=(ArithmeticFunction.moebius (p*k) : ℝ)/(p*k : ℕ) by rfl,primeMu p k hp]
    by_cases h : p ∣ k <;> simp [h,f,div_eq_mul_inv,mul_comm]
    ring
  rw [pref p U,pref 1 U,pref p (U/p)]
  have unit1 (n : ℕ) : IsUnit (n : ZMod 1) := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim ..]
    exact isUnit_one
  simp_rw [if_pos (unit1 _)]
  simp only [unitp]
  have pos := sum_filter_add_sum_filter_not (range (U+1)) (fun n => p ∣ n) f
  rw [sumMultiples p U hp.pos] at pos
  simp_rw [ev] at pos
  rw [← sum_div,sum_neg_distrib,sum_filter] at pos
  linear_combination pos

theorem solution (p : ℕ) [NeZero p] (hp : p.Prime) :
    (∀ (N : ℕ) (x : ℚ), (p : ℂ)*transform false N x + primeSquareShifts p N x +
      shifts p (p*N) (x/p) = 0) ∧
    (∀ U : ℕ, GRH.reducedMoebiusHarmonic p U = GRH.reducedMoebiusHarmonic 1 U +
      GRH.reducedMoebiusHarmonic p (U/p)/(p : ℝ)) := by
  refine ⟨?_,fun U => harmonic p U hp⟩
  intro N x
  rw [squareShifts p N hp x,shiftFilter,liftMultiples p N hp x]
  ring
