-- Prove2me | solution 1 for FamousTheorems.erdos_ko_rado
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:17:50.118742+00:00
-- url     : https://prove2.me/submissions/a8cbcb3f-22b2-4e68-b9c6-9aacba80684b

import Mathlib

theorem solution {n r : ℕ} {𝒜 : Finset (Finset (Fin n))} (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hr𝒜 : (𝒜 : Set (Finset (Fin n))).Sized r) (hr : r ≤ n / 2) : 𝒜.card ≤ (n - 1).choose (r - 1) :=
  Finset.erdos_ko_rado h𝒜 hr𝒜 hr
