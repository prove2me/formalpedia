-- Prove2me | solution 2 for BookProof.SirkCertifiedGap.resolvent_commutes_parity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T19:37:43.057812+00:00
-- url     : https://prove2.me/submissions/ad8959f2-cd73-4d79-8a5b-11d1c3b78e3c

-- Generated from ChapterSirkCertifiedGap.lean — solution of BookProof.SirkCertifiedGap.resolvent_commutes_parity
import Mathlib
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap











noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution {T P R : E →ₗ[ℂ] E} {z : ℂ}
    (hcomm : ∀ x, T (P x) = P (T x))
    (hR1 : ∀ x, R (T x - z • x) = x) (hR2 : ∀ x, T (R x) - z • R x = x) (x : E) :
    R (P x) = P (R x) := by

  have hx : P x = T (P (R x)) - z • P (R x) := by
    have h1 : P (T (R x) - z • R x) = P x := by rw [hR2]
    rw [map_sub, map_smul, ← hcomm] at h1
    exact h1.symm
  rw [hx, hR1]
