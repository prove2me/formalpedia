-- Prove2me | solution 1 for GRH.prime_residue_mean_square_relative_to_the_modulus_one_bilinear_sum
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T06:06:44.735055+00:00
-- url     : https://prove2.me/submissions/f4fe06e8-a23e-4d23-962e-125f2b60099f

import Theorems.Thm_GRH_prime_square_fourier_filter_and_coprime_harmonic_recursion
import Theorems.Thm_GRH_centered_moebius_uniform_large_modulus_range
import Theorems.Thm_GRH_moebius_large_sieve_energy_and_exceptional_farey_count
import Theorems.Thm_Helfgott_coprime_mobius_reciprocal_le_one
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Finset GRH.AdditiveMoebiusSpectrum GRH.SquarefullFrequencies

private theorem harmonicBound (q U : ℕ) [NeZero q] : |GRH.reducedMoebiusHarmonic q U| ≤ 1 := by
  have hi : Ioc 0 U = Icc 1 U := by ext k; simp; omega
  simpa only [GRH.reducedMoebiusHarmonic,hi,ZMod.isUnit_iff_coprime] using
    Helfgott.coprime_mobius_reciprocal_le_one q U

private theorem harmonicDiff (p : Nat.Primes) (U : ℕ) :
    |(GRH.reducedMoebiusHarmonic 1 U)^2-(primeHarmonic p U)^2| ≤ 2/(p.val : ℝ) := by
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  let x := GRH.reducedMoebiusHarmonic 1 U
  let y := primeHarmonic p U
  have hp : 0 < (p.val : ℝ) := by exact_mod_cast p.property.pos
  have hr := (GRH.prime_square_fourier_filter_and_coprime_harmonic_recursion p.val p.property).2 U
  change y=x+_ at hr
  have hsub : |x-y| ≤ 1/(p.val : ℝ) := by
    rw [show x-y = -(GRH.reducedMoebiusHarmonic p.val (U/p.val)/(p.val : ℝ)) by linarith only [hr],
      abs_neg,abs_div,abs_of_pos hp]
    exact div_le_div_of_nonneg_right (harmonicBound p.val _) hp.le
  have hx : |x| ≤ 1 := harmonicBound 1 U
  have hy : |y| ≤ 1 := harmonicBound p.val U
  have Hadd : |x+y| ≤ 2 :=
    (abs_add_le x y).trans (by linarith only [hx,hy])
  change |x^2-y^2| ≤ _
  rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul]
  calc
    _ ≤ (1/(p.val : ℝ))*2 := mul_le_mul hsub Hadd (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem energyIdentity (p : Nat.Primes) (N : ℕ) :
    (p.val : ℝ)*relativeVariance p N = (p.val : ℝ)*primeVariance p N +
      ((N : ℝ)*((GRH.reducedMoebiusHarmonic 1 N.sqrt)^2-
        (primeHarmonic p N.sqrt)^2))^2 := by
  classical
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  let B := fun a : ZMod p.val => GRH.centeredMoebiusBilinear p.val a N
  let M := GRH.centeredMoebiusBilinear 1 0 N
  let m := (∑ a, B a)/(p.val : ℝ)
  let b := M/(p.val : ℝ)
  let D := (GRH.reducedMoebiusHarmonic 1 N.sqrt)^2 - (primeHarmonic p N.sqrt)^2
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hf : (∑ a : ZMod p.val, fiber a N (weight true N)) = ∑ n ∈ range (N+1), weight true N n := by
    unfold fiber
    rw [sum_comm]
    simp
  have hf1 : fiber (0 : ZMod 1) N (weight true N) = ∑ n ∈ range (N+1), weight true N n := by
    unfold fiber
    exact sum_congr rfl (fun n _ => if_pos (Subsingleton.elim ..))
  have hs : (∑ a, B a) + (p.val : ℝ)*correction p.val N = M + correction 1 N := by
    calc
      _ = ∑ a : ZMod p.val, (B a+correction p.val N) := by simp [sum_add_distrib,ZMod.card]
      _ = ∑ a : ZMod p.val, fiber a N (weight true N) :=
        sum_congr rfl (fun a _ => (GRH.centered_moebius_uniform_large_modulus_range p.val a N).1)
      _ = fiber (0 : ZMod 1) N (weight true N) := hf.trans hf1.symm
      _ = _ := (GRH.centered_moebius_uniform_large_modulus_range 1 0 N).1.symm
  have ps : (p.val : ℝ)*m=∑ a, B a := by dsimp [m]; field_simp
  have pb : (p.val : ℝ)*b=M := by dsimp [b]; field_simp
  have hd : (p.val : ℝ)*(m-b)=(N : ℝ)*D := by
    change (∑ a, B a) + (p.val : ℝ)*((N : ℝ)/p.val*(primeHarmonic p N.sqrt)^2) =
      M+(N : ℝ)/(1 : ℕ)*(GRH.reducedMoebiusHarmonic 1 N.sqrt)^2 at hs
    rw [Nat.cast_one,div_one] at hs
    have pc : (p.val : ℝ)*((N : ℝ)/p.val*(primeHarmonic p N.sqrt)^2) =
        (N : ℝ)*(primeHarmonic p N.sqrt)^2 := by field_simp
    rw [pc] at hs
    dsimp [D]
    rw [mul_sub,ps,pb]
    linarith only [hs]
  have sumzero : ∑ a : ZMod p.val, (B a-m)=0 := by
    rw [sum_sub_distrib]
    simpa only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] using sub_eq_zero.mpr ps.symm
  have center : relativeVariance p N = primeVariance p N+(p.val : ℝ)*(m-b)^2 := by
    change (∑ a, (B a-b)^2) = (∑ a, (B a-m)^2)+_
    calc
      _ = ∑ a, ((B a-m)^2 + (B a-m)*(2*(m-b)) + (m-b)^2) :=
        sum_congr rfl (fun a _ => by ring)
      _ = _ := by rw [sum_add_distrib,sum_add_distrib,← sum_mul,sumzero]; simp [ZMod.card]
  change _ = _+((N : ℝ)*D)^2
  rw [center,← hd]
  ring

private theorem exceptionalBound (p : Nat.Primes) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (exceptionalResidues p N T : ℝ)*T^2 ≤ relativeVariance p N := by
  classical
  let : NeZero p.val := ⟨p.property.ne_zero⟩
  let v := fun a : ZMod p.val => GRH.centeredMoebiusBilinear p.val a N -
    GRH.centeredMoebiusBilinear 1 0 N/(p.val : ℝ)
  let A := (univ : Finset (ZMod p.val)).filter fun a => T < |v a|
  change (A.card : ℝ)*T^2 ≤ ∑ a, (v a)^2
  calc
    _ = ∑ _a ∈ A, T^2 := by simp
    _ ≤ ∑ a ∈ A, (v a)^2 := by
      apply sum_le_sum
      intro a ha
      simpa only [sq_abs] using pow_le_pow_left₀ hT (mem_filter.mp ha).2.le 2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

theorem solution :
    (∀ (p : Nat.Primes) (N : ℕ), (p.val : ℝ)*relativeVariance p N = (p.val : ℝ)*primeVariance p N +
      ((N : ℝ)*((GRH.reducedMoebiusHarmonic 1 N.sqrt)^2-
        (primeHarmonic p N.sqrt)^2))^2) ∧
    (∀ (Q N : ℕ), 0 < Q → ∀ P : Finset Nat.Primes, (∀ p ∈ P, Q < p.val ∧ p.val ≤ 2*Q) →
      (∑ p ∈ P, (p.val : ℝ)*relativeVariance p N) ≤ (4*(Q : ℝ)^2+13*((N : ℝ)+1))*N+4*(N : ℝ)^2/Q ∧
      ∀ T : ℝ, 0 ≤ T → (Q : ℝ)*T^2*(∑ p ∈ P, (exceptionalResidues p N T : ℝ)) ≤
        (4*(Q : ℝ)^2+13*((N : ℝ)+1))*N+4*(N : ℝ)^2/Q) := by
  classical
  refine ⟨energyIdentity,?_⟩
  intro Q N hQ P hP
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcard : P.card ≤ Q := by
    have h := card_le_card_of_injOn (s:=P) (t:=Ioc Q (2*Q)) (fun p => p.val)
      (fun p hp => mem_Ioc.mpr (hP p hp)) (fun _ _ _ _ eq => Subtype.ext eq)
    rw [Nat.card_Ioc] at h
    omega
  let K : ℝ := (2*N/(Q : ℝ))^2
  have hrow (p : Nat.Primes) (h : p ∈ P) : (p.val : ℝ)*relativeVariance p N ≤
      (p.val : ℝ)*primeVariance p N+K := by
    rw [energyIdentity]
    apply add_le_add le_rfl
    have hqp : (Q : ℝ) ≤ p.val := by exact_mod_cast (hP p h).1.le
    let D := (GRH.reducedMoebiusHarmonic 1 N.sqrt)^2 - (primeHarmonic p N.sqrt)^2
    have hd : |D| ≤ 2/(Q : ℝ) := (harmonicDiff p N.sqrt).trans
      (div_le_div_of_nonneg_left (by norm_num) hQ' hqp)
    have ha : |(N : ℝ)*D| ≤ 2*N/(Q : ℝ) := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)).trans_eq (by ring)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hbase := (GRH.moebius_large_sieve_energy_and_exceptional_farey_count (2*Q) N (by omega)).2 P
    (fun p h => (hP p h).2)
  have htotal : (∑ p ∈ P, (p.val : ℝ)*relativeVariance p N) ≤
      (4*(Q : ℝ)^2+13*((N : ℝ)+1))*N+4*(N : ℝ)^2/Q := by
    calc
      _ ≤ ∑ p ∈ P, ((p.val : ℝ)*primeVariance p N+K) := sum_le_sum hrow
      _ = (∑ p ∈ P, (p.val : ℝ)*primeVariance p N)+(P.card : ℝ)*K := by simp [sum_add_distrib]
      _ ≤ (((2*Q : ℕ) : ℝ)^2+13*((N : ℝ)+1))*N+(Q : ℝ)*K :=
        add_le_add hbase (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _))
      _ = _ := by dsimp [K]; push_cast; field_simp; ring
  refine ⟨htotal,fun T hT => ?_⟩
  apply le_trans _ htotal
  rw [mul_sum]
  apply sum_le_sum
  intro p h
  have hqp : (Q : ℝ) ≤ p.val := by exact_mod_cast (hP p h).1.le
  calc
    _ = (Q : ℝ)*((exceptionalResidues p N T : ℝ)*T^2) := by ring
    _ ≤ (p.val : ℝ)*((exceptionalResidues p N T : ℝ)*T^2) :=
      mul_le_mul_of_nonneg_right hqp (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (exceptionalBound p N T hT) (Nat.cast_nonneg _)
