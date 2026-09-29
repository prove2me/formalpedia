-- Prove2me | solution 1 for FamousTheorems.fraisse_limit_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:07:39.291982+00:00
-- url     : https://prove2.me/submissions/305e22ff-9e8a-4469-b70c-f6c42fb1d814

import Mathlib

universe u

theorem solution {L : FirstOrder.Language} {K : Set (CategoryTheory.Bundled L.Structure)} {M N : Type u}
    [L.Structure M] [L.Structure N] [Countable ((l : ℕ) × L.Functions l)] [Countable M] [Countable N]
    (hM : FirstOrder.Language.IsFraisseLimit K M) (hN : FirstOrder.Language.IsFraisseLimit K N) :
    Nonempty (L.Equiv M N) :=
  hM.nonempty_equiv hN
