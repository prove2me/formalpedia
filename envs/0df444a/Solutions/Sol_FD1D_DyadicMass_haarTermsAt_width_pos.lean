-- Prove2me | solution 1 for FD1D.DyadicMass.haarTermsAt_width_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:07.158819+00:00
-- url     : https://prove2.me/submissions/8efe7c2e-94d4-4cfc-83bc-c577dbe43fcc

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
namespace DyadicMass
theorem _root_.solution
    {L : ℕ} (q : DyadicMass L) {a p : ℝ} (hp : 0 < p)
    {t : HaarTerm} (ht : t ∈ q.haarTermsAt a p) :
    0 < t.width := by
  induction q generalizing a p with
  | leaf =>
      simp [haarTermsAt] at ht
  | @branch L l r ihl ihr =>
      simp only [haarTermsAt, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | ht | ht
      · exact hp
      · exact ihl (by positivity) ht
      · exact ihr (by positivity) ht
end DyadicMass
end FD1D
