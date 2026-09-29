-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:05:51.017476+00:00
-- url     : https://prove2.me/submissions/ca33a5f8-28d6-4705-85a5-41207a75a3a9

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — solution of BookProof.ChapterSirkTrotterKato.flow_tendsto_of_strong_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_strongResolventConvergence_ofBounded
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendsto
open BookProof.ChapterSirkTrotterKato









noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H}
    (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim)
    (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) (v : H) (t : ℝ) :
    Tendsto (fun n => (ofBounded (A n) (hA n)).stoneU t v) atTop
      (𝓝 ((ofBounded Alim hlim).stoneU t v)) := trotterKato_tendsto _ _ (strongResolventConvergence_ofBounded hA hlim hconv) v t
