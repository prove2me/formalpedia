-- Prove2me | solution 1 for FamousTheorems.chevalley_constructible_image
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:51.340788+00:00
-- url     : https://prove2.me/submissions/37184559-fe29-455d-96f4-0f4416db8a7c

import Mathlib

theorem solution {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.FinitePresentation)
    {s : Set (PrimeSpectrum S)} (hs : Topology.IsConstructible s) :
    Topology.IsConstructible (PrimeSpectrum.comap f '' s) :=
  PrimeSpectrum.isConstructible_comap_image hf hs
