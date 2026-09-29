-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.flow_transfer_of_strong_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:05:51.591416+00:00
-- url     : https://prove2.me/submissions/33b26e23-1c52-41e2-949c-94eb6b30fc79

-- Generated from ChapterSirkTrotterKatoGalerkin.lean — solution of BookProof.ChapterSirkTrotterKato.flow_transfer_of_strong_tendsto
import Mathlib
import Definitions.Def_ChapterSirkTrotterKatoGalerkin
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_strongResolventConvergence_ofBounded
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_trotterKato_tendstoUniformlyOn
open BookProof.ChapterSirkTrotterKato









noncomputable section

open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterUnitaryTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution {A : ℕ → H →L[ℂ] H} {Alim : H →L[ℂ] H}
    (hA : ∀ n, IsSelfAdjoint (A n)) (hlim : IsSelfAdjoint Alim)
    (hconv : ∀ u : H, Tendsto (fun n => A n u) atTop (𝓝 (Alim u))) (v : H)
    {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    TendstoUniformlyOn (fun n t => (ofBounded (A n) (hA n)).stoneU t v)
      (fun t => (ofBounded Alim hlim).stoneU t v) atTop (Set.Icc (-T₀) T₀) := trotterKato_tendstoUniformlyOn _ _ (strongResolventConvergence_ofBounded hA hlim hconv) v hT₀
