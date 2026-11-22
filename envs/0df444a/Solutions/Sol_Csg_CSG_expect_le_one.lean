-- Prove2me | solution 1 for Csg.CSG.expect_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:35.878452+00:00
-- url     : https://prove2.me/submissions/92b2776d-1270-422a-92c1-64705e333fec

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {a1 : A1} {a2 : A2} {v : S → ℝ} (hv : ∀ s', v s' ≤ 1) :
    C.expect s a1 a2 v ≤ 1 := by
  unfold expect
  have hmass : (∑ s' : S, C.K s a1 a2 s').toReal ≤ 1 := by
    have hle : (∑ s' : S, C.K s a1 a2 s') ≤ 1 := by
      calc ∑ s' : S, C.K s a1 a2 s' ≤ ∑' s', C.K s a1 a2 s' := ENNReal.sum_le_tsum Finset.univ
        _ = 1 := (C.K s a1 a2).tsum_coe
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
  calc ∑ s' : S, (C.K s a1 a2 s').toReal * v s'
      ≤ ∑ s' : S, (C.K s a1 a2 s').toReal * 1 :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hv s') ENNReal.toReal_nonneg
    _ = ∑ s' : S, (C.K s a1 a2 s').toReal := by simp
    _ = (∑ s' : S, C.K s a1 a2 s').toReal :=
        (ENNReal.toReal_sum fun s' _ => (C.K s a1 a2).apply_ne_top s').symm
    _ ≤ 1 := hmass
end Csg.CSG
