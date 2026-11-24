-- Prove2me | solution 1 for BB6Kit.indep_or_smooth
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T22:22:05.481848+00:00
-- url     : https://prove2.me/submissions/387b8a3e-33a1-4d9d-8874-e2c137393b33

import Mathlib
import Definitions.Def_BB6Kit

theorem solution (c : ℕ) (hc : 0 < c) :
    BB6Kit.MultIndep 2 c 3 ∨ ∃ a b : ℕ, c = 2 ^ a * 3 ^ b := by
  by_cases hsm : ∃ a b : ℕ, c = 2 ^ a * 3 ^ b
  · exact Or.inr hsm
  left
  have hp : ∃ p, p.Prime ∧ p ∣ c ∧ p ≠ 2 ∧ p ≠ 3 := by
    by_contra hno
    push_neg at hno
    apply hsm
    refine ⟨c.factorization 2, c.factorization 3, ?_⟩
    have hsub : c.factorization.support ⊆ {2, 3} := by
      intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpd, _⟩ := hp
      by_cases h2 : p = 2
      · simp [h2]
      · have := hno p hpp hpd h2
        simp [this]
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hc.ne']
    rw [Finsupp.prod_of_support_subset _ hsub _ (by intro i _; simp)]
    rw [Finset.prod_pair (by norm_num)]
  obtain ⟨p, hpp, hpd, hp2, hp3⟩ := hp
  intro x y z hxyz
  have hz : ∀ b : ℝ, b ≠ 0 → ∀ w : ℤ, b ^ w = b ^ w.toNat / b ^ (-w).toNat := by
    intro b hb w
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hb]
    congr 1
    exact (Int.toNat_sub_toNat_neg w).symm
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [hz _ (by norm_num) x, hz _ hc' y, hz _ (by norm_num) z, div_mul_div_comm, div_mul_div_comm,
    div_eq_one_iff_eq (by positivity)] at hxyz
  have hN : 2 ^ x.toNat * c ^ y.toNat * 3 ^ z.toNat = 2 ^ (-x).toNat * c ^ (-y).toNat * 3 ^ (-z).toNat := by
    exact_mod_cast hxyz
  have hcp : ∀ b : ℕ, c ^ b ≠ 0 := fun b => (pow_pos hc b).ne'
  have hfac : ∀ q a b d : ℕ, (2 ^ a * c ^ b * 3 ^ d).factorization q =
      a * (2 : ℕ).factorization q + b * c.factorization q + d * (3 : ℕ).factorization q := by
    intro q a b d
    rw [Nat.factorization_mul (mul_ne_zero (by positivity) (hcp b)) (by positivity),
      Nat.factorization_mul (by positivity) (hcp b)]
    simp [Nat.factorization_pow]
  have hv := congrArg (fun n => n.factorization p) hN
  have hv2 := congrArg (fun n => n.factorization 2) hN
  have hv3 := congrArg (fun n => n.factorization 3) hN
  simp only [hfac] at hv hv2 hv3
  have f2p : (2 : ℕ).factorization p = 0 := by
    rw [Nat.prime_two.factorization, Finsupp.single_apply]; simp [Ne.symm hp2]
  have f3p : (3 : ℕ).factorization p = 0 := by
    rw [Nat.prime_three.factorization, Finsupp.single_apply]; simp [Ne.symm hp3]
  have f22 : (2 : ℕ).factorization 2 = 1 := by simp [Nat.prime_two.factorization]
  have f32 : (3 : ℕ).factorization 2 = 0 := by
    rw [Nat.prime_three.factorization, Finsupp.single_apply]; simp
  have f23 : (2 : ℕ).factorization 3 = 0 := by
    rw [Nat.prime_two.factorization, Finsupp.single_apply]; simp
  have f33 : (3 : ℕ).factorization 3 = 1 := by simp [Nat.prime_three.factorization]
  have hvp : 0 < c.factorization p := hpp.factorization_pos_of_dvd hc.ne' hpd
  rw [f2p, f3p] at hv
  rw [f22, f32] at hv2
  rw [f23, f33] at hv3
  have hy : y.toNat = (-y).toNat := by
    have : y.toNat * c.factorization p = (-y).toNat * c.factorization p := by linarith
    exact Nat.eq_of_mul_eq_mul_right hvp this
  rw [hy] at hv2 hv3
  have hx : x.toNat = (-x).toNat := by linarith
  have hzz : z.toNat = (-z).toNat := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := Int.toNat_sub_toNat_neg x; omega
  · have := Int.toNat_sub_toNat_neg y; omega
  · have := Int.toNat_sub_toNat_neg z; omega
