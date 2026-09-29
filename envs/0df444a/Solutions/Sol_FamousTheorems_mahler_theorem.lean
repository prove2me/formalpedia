-- Prove2me | solution 1 for FamousTheorems.mahler_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:17:41.617347+00:00
-- url     : https://prove2.me/submissions/8a6b0944-47c2-44e4-857c-de148cb08388

import Mathlib

theorem solution {p : ℕ} [Fact p.Prime] {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] (f : C(ℤ_[p], E)) :
    HasSum (fun n : ℕ => PadicInt.mahlerTerm ((fwdDiff 1)^[n] f 0) n) f :=
  PadicInt.hasSum_mahler f
