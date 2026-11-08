-- Prove2me | solution 1 for FamilyGenTest.rdelta_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T13:52:44.153736+00:00
-- url     : https://prove2.me/submissions/7876f182-90c6-4ef6-9bf4-ccfb0ffa40af

import Mathlib
import Definitions.Def_FamilyGenTest_Rewards

open FamilyGenTest in
theorem solution {I : Type*} (R : Rewards I) (hR : CensoredOrder R) (i : I) :
    0 ≤ rdelta R i := by
  obtain ⟨h1, h2⟩ := hR i
  unfold rdelta
  linarith
