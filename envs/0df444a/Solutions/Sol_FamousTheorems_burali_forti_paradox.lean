-- Prove2me | solution 1 for FamousTheorems.burali_forti_paradox
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:13:23.963861+00:00
-- url     : https://prove2.me/submissions/93cca1ab-d426-4597-827c-5e1b53dc0d84

import Mathlib

theorem solution :
    ¬∃ x : ZFSet, ∀ y : ZFSet, y ∈ x ↔ y.IsOrdinal :=
  fun ⟨x, hx⟩ => ZFSet.isOrdinal_notMem_univ ⟨x, funext fun y => propext (hx y), trivial⟩
