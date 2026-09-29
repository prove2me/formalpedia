-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.isCompact_orbit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:14:20.15463+00:00
-- url     : https://prove2.me/submissions/79504af5-ce69-4065-9a9e-b81aeb416476

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.isCompact_orbit
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (y : H) (T₀ : ℝ) :
    IsCompact ((fun s : ℝ => T.stoneU s y) '' Set.Icc (-T₀) T₀) := (isCompact_Icc).image (T.continuous_stoneU_apply y)
