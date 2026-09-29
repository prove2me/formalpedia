-- Prove2me | solution 1 for BookProof.BandEnclosure.band_enclosure_of_nested
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:37:46.124194+00:00
-- url     : https://prove2.me/submissions/1c70efd8-a0a7-4fe7-9aee-fb20571e77fe

import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology
set_option autoImplicit false

theorem solution {lo hi a : ℕ → ℝ} {lam : ℝ}
    (hnest : ∀ m, Set.Icc (lo (m + 1)) (hi (m + 1)) ⊆ Set.Icc (lo m) (hi m))
    (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m))
    (hconv : Tendsto a atTop (𝓝 lam)) :
    ∀ m, lam ∈ Set.Icc (lo m) (hi m) := by
  intro m
  apply isClosed_Icc.mem_of_tendsto hconv
  filter_upwards [eventually_ge_atTop m] with n hmn
  have hsub : Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by
    induction n, hmn using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ n _ ih => exact Set.Subset.trans (hnest n) ih
  exact hsub (hmem n)

#print axioms solution
