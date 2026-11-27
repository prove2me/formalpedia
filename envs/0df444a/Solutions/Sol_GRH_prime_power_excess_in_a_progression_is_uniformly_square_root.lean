-- Prove2me | solution 1 for GRH.prime_power_excess_in_a_progression_is_uniformly_square_root
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:22:12.915477+00:00
-- url     : https://prove2.me/submissions/b58b1f45-eec6-4ca2-8eaa-5e5d608cb94f

import Definitions.Def_GRH_PrimeDeficitMean

open Finset ArithmeticFunction GRH.SplitPrimeLower

theorem solution : ∃ K : ℝ, 0 ≤ K ∧ ∀ q n : ℕ,
    0 ≤ mangoldtWeight q n - primeWeight q n ∧
    mangoldtWeight q n - primeWeight q n ≤ K * Real.sqrt n := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0,le_max_right ..,fun q n => ?_⟩
  have comp (p : ℕ) :
      0 ≤ vonMangoldt.residueClass (1:ZMod q) p -
        (if p.Prime ∧ (p:ZMod q)=1 then Real.log p else 0) ∧
      vonMangoldt.residueClass (1:ZMod q) p - (if p.Prime ∧ (p:ZMod q)=1 then Real.log p else 0)
        ≤ vonMangoldt p - (if p.Prime then Real.log p else 0) := by
    classical
    by_cases hp : p.Prime
    · by_cases ha : (p:ZMod q)=1 <;>
        simp [hp,ha,vonMangoldt.residueClass,vonMangoldt_apply_prime hp]
    · simpa [hp] using And.intro (vonMangoldt.residueClass_nonneg (1:ZMod q) p)
        (vonMangoldt.residueClass_le (1:ZMod q) p)
  unfold mangoldtWeight primeWeight
  rw [← sum_sub_distrib]
  refine ⟨sum_nonneg (fun i _ => (comp i).1),?_⟩
  calc
    _ ≤ ∑ i ∈ Icc 1 n, (vonMangoldt i - (if i.Prime then Real.log i else 0)) :=
      sum_le_sum (fun i _ => (comp i).2)
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [sum_sub_distrib,Chebyshev.psi,Chebyshev.theta,Nat.floor_natCast,
        show Icc 1 n = Ioc 0 n from Icc_succ_left_eq_Ioc 0 n,Finset.sum_filter]
    _ ≤ _ := (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.sqrt_nonneg _))
