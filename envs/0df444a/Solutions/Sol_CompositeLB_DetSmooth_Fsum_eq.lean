-- Prove2me | solution 1 for CompositeLB.DetSmooth.Fsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:00:28.434909+00:00
-- url     : https://prove2.me/submissions/9e14804e-595f-4716-848f-140109178e63

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Construction

set_option autoImplicit false

open CompositeLB.DetSmooth

theorem solution {m d k : ℕ} (a : ℝ) (v : ℕ → CompositeLB.DetLip.E d)
    (δ : Fin m → ℕ → ℝ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hv : Orthonormal ℝ (fun r : Fin (k + 1) => v (r : ℕ)))
    (hδ : ∀ i r, δ i r = 0 ∨ δ i r = 1)
    (hsum : ∀ r ∈ Finset.Icc 1 k,
      ∑ i : Fin m, δ i r = ((m / 2 : ℕ) : ℝ)) :
    (∀ x : CompositeLB.DetLip.E d, CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) x = Fsum m a v (k + 1) x) ∧
    (∀ q : ℕ, 1 ≤ q → q ≤ k → ∀ x : CompositeLB.DetLip.E d,
      (∀ r : ℕ, q ≤ r → r ≤ k → inner ℝ x (v r) = 0) →
      Fsum m a v q x = CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) x) := by
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    exact this.ne'
  have hs1 : ∑ i : Fin m, δ i 1 = ((m / 2 : ℕ) : ℝ) := hsum 1 (Finset.mem_Icc.2 ⟨le_rfl, hk⟩)
  have hsk : ∑ i : Fin m, δ i k = ((m / 2 : ℕ) : ℝ) := hsum k (Finset.mem_Icc.2 ⟨hk, le_rfl⟩)
  have key : ∀ x : CompositeLB.DetLip.E d, CompositeLB.DetLip.avgF (fun i => hardF a k v (δ i)) x =
      ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ)) *
        ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0)) +
          (∑ r ∈ Finset.Icc 1 k, (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2) +
          (inner ℝ x (v k)) ^ 2) := by
    intro x
    unfold CompositeLB.DetLip.avgF hardF
    have e : ∑ i : Fin m, 1 / 8 * (δ i 1 * ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0))) +
        (∑ r ∈ Finset.Icc 1 k, δ i r * (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2) +
        δ i k * (inner ℝ x (v k)) ^ 2)
        = 1 / 8 * ((∑ i : Fin m, δ i 1) * ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0))) +
          (∑ r ∈ Finset.Icc 1 k, (∑ i : Fin m, δ i r) * (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2) +
          (∑ i : Fin m, δ i k) * (inner ℝ x (v k)) ^ 2) := by
      have e1 : ∑ i : Fin m, ∑ r ∈ Finset.Icc 1 k,
          δ i r * (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2
          = ∑ r ∈ Finset.Icc 1 k, (∑ i : Fin m, δ i r) *
            (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun r _ => (Finset.sum_mul _ _ _).symm)
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
        ← Finset.sum_mul, e1]
    rw [e, hs1, hsk, Finset.sum_congr rfl (fun r hr => by rw [hsum r hr]), ← Finset.mul_sum]
    field_simp
  have hFs : ∀ x : CompositeLB.DetLip.E d, Fsum m a v (k + 1) x =
      ((m / 2 : ℕ) : ℝ) / (8 * (m : ℝ)) *
        ((inner ℝ x (v 0)) ^ 2 - 2 * a * (inner ℝ x (v 0)) +
          (∑ r ∈ Finset.Icc 1 k, (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2) +
          (inner ℝ x (v k)) ^ 2) := by
    intro x
    unfold Fsum
    have : Finset.Ico 1 (k + 1) = Finset.Icc 1 k := by
      ext r; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [this]
    simp
  refine ⟨fun x => by rw [key, hFs], ?_⟩
  intro q hq1 hqk x hx
  rw [key]
  unfold Fsum
  congr 1
  have hsplit : ∑ r ∈ Finset.Icc 1 k, (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2
      = ∑ r ∈ Finset.Ico 1 q, (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2
        + ∑ r ∈ Finset.Ico q (k + 1), (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2 := by
    have : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
      ext r; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [this, Finset.sum_Ico_consecutive _ hq1 (by omega)]
  have htail : ∑ r ∈ Finset.Ico q (k + 1), (inner ℝ x (v (r - 1)) - inner ℝ x (v r)) ^ 2
      = (inner ℝ x (v (q - 1))) ^ 2 := by
    rw [Finset.sum_eq_single q]
    · rw [hx q le_rfl hqk]; simp
    · intro r hr hrq
      have hr' := Finset.mem_Ico.1 hr
      rw [hx r hr'.1 (by omega), hx (r - 1) (by omega) (by omega)]
      simp
    · intro h; exact absurd (Finset.mem_Ico.2 ⟨le_rfl, by omega⟩) h
  rw [hsplit, htail, hx k hqk le_rfl]
  ring
