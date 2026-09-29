-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.resolvent_commutes_parity
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:16:15.357011+00:00
-- url     : https://prove2.me/submissions/f7573bb3-19c2-4eb3-ab47-f4782a5caabf

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.resolvent_commutes_parity
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P R : E →ₗ[ℂ] E} {z : ℂ}
    (hcomm : ∀ x, T (P x) = P (T x))
    (hR1 : ∀ x, R (T x - z • x) = x) (hR2 : ∀ x, T (R x) - z • R x = x) (x : E) :
    R (P x) = P (R x) := by
  calc
    R (P x) = R (P (T (R x) - z • R x)) := by rw [hR2]
    _ = R (T (P (R x)) - z • P (R x)) := by
      rw [map_sub, map_smul, ← hcomm]
    _ = P (R x) := hR1 _

#print axioms solution
