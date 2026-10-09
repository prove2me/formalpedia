-- Prove2me | solution 1 for BookProof.ChapterF1.field_gauge_invariant_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:56:56.887437+00:00
-- url     : https://prove2.me/submissions/cf983bcb-d881-45e5-b325-65ca6258b912

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.field_gauge_invariant_iff
import Mathlib
import Definitions.Def_ChapterF1
import Theorems.Thm_BookProof_ChapterG2_brst_physical_iff_gauge_invariant
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (Q : ℂ[X]) (a : ℂ[X]) :
    (![a, 0] ∈ BookProof.ChapterG2.brstKer Q) ↔ Q * a = 0 := BookProof.ChapterG2.brst_physical_iff_gauge_invariant Q a
