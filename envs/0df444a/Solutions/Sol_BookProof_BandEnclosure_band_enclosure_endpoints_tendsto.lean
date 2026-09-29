-- Prove2me | solution 1 for BookProof.BandEnclosure.band_enclosure_endpoints_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:17.21062+00:00
-- url     : https://prove2.me/submissions/18a4bf72-5e96-49cb-b575-a4d4fcdd9e97

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
open Filter Topology
set_option autoImplicit false

theorem solution {lo hi a : ℕ → ℝ} {lam : ℝ}
    (hnest : ∀ m, Set.Icc (lo (m + 1)) (hi (m + 1)) ⊆ Set.Icc (lo m) (hi m))
    (hmem : ∀ m, a m ∈ Set.Icc (lo m) (hi m))
    (hconv : Tendsto a atTop (𝓝 lam))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    (∀ m, lam ∈ Set.Icc (lo m) (hi m)) ∧
      (∀ lam', (∀ m, lam' ∈ Set.Icc (lo m) (hi m)) → lam' = lam) ∧
      Tendsto lo atTop (𝓝 lam) ∧ Tendsto hi atTop (𝓝 lam) := by
  have hb : ∀ m, lam ∈ Set.Icc (lo m) (hi m) := by
    intro m
    apply isClosed_Icc.mem_of_tendsto hconv
    filter_upwards [eventually_ge_atTop m] with n hmn
    have hsub : Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by
      induction n, hmn using Nat.le_induction with
      | base => exact Set.Subset.rfl
      | succ n _ ih => exact Set.Subset.trans (hnest n) ih
    exact hsub (hmem n)
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro lam' hb'
    have hle : lam - lam' ≤ 0 := ge_of_tendsto hwidth (Eventually.of_forall (fun m => by
      rcases hb m with ⟨_, hu⟩
      rcases hb' m with ⟨hl', _⟩
      linarith))
    have hge : lam' - lam ≤ 0 := ge_of_tendsto hwidth (Eventually.of_forall (fun m => by
      rcases hb m with ⟨hl, _⟩
      rcases hb' m with ⟨_, hu'⟩
      linarith))
    linarith
  · have hlim : Tendsto (fun m => lam - (hi m - lo m)) atTop (𝓝 lam) := by
      simpa using tendsto_const_nhds.sub hwidth
    exact hlim.squeeze tendsto_const_nhds (fun m => by have h := (hb m).2; linarith)
      (fun m => (hb m).1)
  · have hlim : Tendsto (fun m => lam + (hi m - lo m)) atTop (𝓝 lam) := by
      simpa using tendsto_const_nhds.add hwidth
    exact tendsto_const_nhds.squeeze hlim (fun m => (hb m).2)
      (fun m => by have h := (hb m).1; linarith)
#print axioms solution
