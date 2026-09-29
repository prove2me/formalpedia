-- Prove2me | solution 1 for FamousTheorems.kruskal_katona
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:17:41.800379+00:00
-- url     : https://prove2.me/submissions/57316f6f-b9c6-42a0-90c9-bd56649b6a04

import Mathlib

theorem solution {n r : ℕ} {𝒜 𝒞 : Finset (Finset (Fin n))} (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r)
    (h𝒞𝒜 : 𝒞.card ≤ 𝒜.card) (h𝒞 : Finset.Colex.IsInitSeg 𝒞 r) :
    (Finset.shadow 𝒞).card ≤ (Finset.shadow 𝒜).card :=
  Finset.kruskal_katona h𝒜r h𝒞𝒜 h𝒞
