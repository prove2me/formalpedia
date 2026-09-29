-- Prove2me | solution 1 for BookProof.BandEnclosure.band_limit_unique
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:37:44.570526+00:00
-- url     : https://prove2.me/submissions/3f03e3a0-27fc-4339-9a5d-9cdb2872fd89

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Filter Topology
set_option autoImplicit false

theorem solution {lo hi : ℕ → ℝ} {lam lam' : ℝ}
    (h : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (h' : ∀ m, lam' ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    lam = lam' := by
  have hle : lam - lam' ≤ 0 := ge_of_tendsto hwidth (Filter.Eventually.of_forall (fun m => by
    rcases h m with ⟨_, hu⟩
    rcases h' m with ⟨hl', _⟩
    linarith))
  have hge : lam' - lam ≤ 0 := ge_of_tendsto hwidth (Filter.Eventually.of_forall (fun m => by
    rcases h m with ⟨hl, _⟩
    rcases h' m with ⟨_, hu'⟩
    linarith))
  linarith

#print axioms solution
