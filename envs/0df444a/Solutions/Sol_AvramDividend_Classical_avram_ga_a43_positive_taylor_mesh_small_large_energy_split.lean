-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a43_positive_taylor_mesh_small_large_energy_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:23:35.16181+00:00
-- url     : https://prove2.me/submissions/5568e7e3-e28b-4aa6-a721-a4d18416a30d

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ga_a42_positive_taylor_small_large_energy_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open BigOperators AvramDividend.Classical

-- Physical finite-mesh positive C2 remainder is controlled by small-modulus total energy and large-cell energy.
theorem solution {ι : Type*} (S : Finset ι) (a z : ι → ℝ)
    (ε M δ : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hε : 0 ≤ ε)
    (hM : ∀ i ∈ S, a i ≤ M)
    (hSmall : ∀ i ∈ S, |z i| < δ → a i ≤ ε) :
    (∑ i ∈ S, a i * (z i)^2) ≤
      ε * (∑ i ∈ S, (z i)^2) +
        M * (∑ i ∈ S, if δ ≤ |z i| then (z i)^2 else 0) := by
  classical
  change Finset.sum S (fun i => a i * (z i)^2) ≤
    ε * Finset.sum S (fun i => (z i)^2) +
    M * Finset.sum S (fun i => if δ ≤ |z i| then (z i)^2 else 0)
  have hPoint (i : ι) (hi : i ∈ S) :
      a i * (z i)^2 ≤
        ε * (z i)^2 + M * (if δ ≤ |z i| then (z i)^2 else 0) :=
    avram_ga_a42_positive_taylor_small_large_energy_split
      (a i) (z i) ε M δ (ha i hi) hε (hM i hi) (hSmall i hi)
  calc
    Finset.sum S (fun i => a i * (z i)^2) ≤
        Finset.sum S (fun i =>
          ε * (z i)^2 + M * (if δ ≤ |z i| then (z i)^2 else 0)) :=
      Finset.sum_le_sum hPoint
    _ = ε * Finset.sum S (fun i => (z i)^2) +
        M * Finset.sum S (fun i =>
          if δ ≤ |z i| then (z i)^2 else 0) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
