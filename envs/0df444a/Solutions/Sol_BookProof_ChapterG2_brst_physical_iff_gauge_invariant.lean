-- Prove2me | solution 1 for BookProof.ChapterG2.brst_physical_iff_gauge_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:21:44.151442+00:00
-- url     : https://prove2.me/submissions/3ed2afb3-57fc-4aa6-a849-f5572a6097c7

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.brst_physical_iff_gauge_invariant
import Mathlib
import Definitions.Def_ChapterG2
open BookProof.ChapterG2



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)

set_option maxHeartbeats 1000000 in
theorem solution (a : A) :
    (![a, 0] ∈ brstKer Q) ↔ Q * a = 0 := by

  convert mem_brstKer_iff Q _
  simp
