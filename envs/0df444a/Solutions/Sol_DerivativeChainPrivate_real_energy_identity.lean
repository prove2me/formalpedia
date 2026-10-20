-- Prove2me | solution 1 for DerivativeChainPrivate.real_energy_identity
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T03:08:50.46268+00:00
-- url     : https://prove2.me/submissions/709f7d24-a792-4403-a613-d4ea3e5a84b4

-- D1 proof: real convex energy identity. No sorry. No self-import.
import Mathlib

open scoped BigOperators

set_option autoImplicit false

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (p a : ι → ℝ) (b : ℝ)
    (hsum : ∑ i ∈ s, p i = 1)
    (hb : b = ∑ i ∈ s, p i * a i) :
    ∑ i ∈ s, p i * (a i - b) ^ 2 = ∑ i ∈ s, p i * (a i) ^ 2 - b ^ 2 := by
  have hexpand : ∀ i : ι, p i * (a i - b) ^ 2
      = p i * (a i) ^ 2 - 2 * b * (p i * a i) + b ^ 2 * p i := by
    intro i
    ring
  have hsum_eq : ∑ i ∈ s, p i * (a i - b) ^ 2
      = ∑ i ∈ s, (p i * (a i) ^ 2 - 2 * b * (p i * a i) + b ^ 2 * p i) :=
    Finset.sum_congr rfl (fun i _ => hexpand i)
  rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmid : ∑ i ∈ s, (2 * b * (p i * a i)) = 2 * b * ∑ i ∈ s, p i * a i := by
    rw [Finset.mul_sum]
  have hlast : ∑ i ∈ s, (b ^ 2 * p i) = b ^ 2 * ∑ i ∈ s, p i := by
    rw [Finset.mul_sum]
  rw [hmid, hlast, ← hb, hsum]
  ring
