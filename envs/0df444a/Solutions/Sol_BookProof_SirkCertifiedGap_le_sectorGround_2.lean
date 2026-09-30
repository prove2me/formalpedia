-- Prove2me | solution 2 for BookProof.SirkCertifiedGap.le_sectorGround
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T19:25:55.566751+00:00
-- url     : https://prove2.me/submissions/c304e3b0-a859-468f-8195-023eba062588

-- Generated from ChapterSirkCertifiedGap.lean — solution of BookProof.SirkCertifiedGap.le_sectorGround
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap











noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T P : E →ₗ[ℂ] E} {s c : ℝ}
    (hne : (sectorRayleighSet T P s).Nonempty)
    (hlb : ∀ x : E, ‖x‖ = 1 → x ∈ paritySector P s → c ≤ rayleigh T x) :
    c ≤ sectorGround T P s := by

  refine le_csInf hne ?_
  rintro r ⟨x, hx, hmem, rfl⟩
  exact hlb x hx hmem
