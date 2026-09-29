-- Prove2me | solution 1 for FamousTheorems.stone_cech_universal_property_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:51:38.829005+00:00
-- url     : https://prove2.me/submissions/112adb91-0e36-4d22-8638-241a6e0bc82c

import Mathlib

theorem solution {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space β] [CompactSpace β] {g : α → β}
    (hg : Continuous g) : ∃ h : StoneCech α → β, Continuous h ∧ h ∘ stoneCechUnit = g :=
  ⟨stoneCechExtend hg, continuous_stoneCechExtend hg, stoneCechExtend_extends hg⟩
