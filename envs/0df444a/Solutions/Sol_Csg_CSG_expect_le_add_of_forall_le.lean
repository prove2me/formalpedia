-- Prove2me | solution 1 for Csg.CSG.expect_le_add_of_forall_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:41.038942+00:00
-- url     : https://prove2.me/submissions/8baebf47-a112-4aea-8ab1-f074d495aadf

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_CsgMonotone

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution {s : S} {a1 : A1} {a2 : A2} {v w : S → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ s', v s' ≤ w s' + ε) : C.expect s a1 a2 v ≤ C.expect s a1 a2 w + ε := by
  unfold expect
  have hmass : (∑ s' : S, (C.K s a1 a2 s').toReal) ≤ 1 := by
    have hle : (∑ s' : S, C.K s a1 a2 s') ≤ 1 := by
      calc ∑ s' : S, C.K s a1 a2 s' ≤ ∑' s', C.K s a1 a2 s' := ENNReal.sum_le_tsum Finset.univ
        _ = 1 := (C.K s a1 a2).tsum_coe
    have h1 : (∑ s' : S, C.K s a1 a2 s').toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
    rwa [ENNReal.toReal_sum fun s' _ => (C.K s a1 a2).apply_ne_top s'] at h1
  calc ∑ s' : S, (C.K s a1 a2 s').toReal * v s'
      ≤ ∑ s' : S, (C.K s a1 a2 s').toReal * (w s' + ε) :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') ENNReal.toReal_nonneg
    _ = ∑ s' : S, ((C.K s a1 a2 s').toReal * w s' + (C.K s a1 a2 s').toReal * ε) :=
        Finset.sum_congr rfl fun s' _ => by ring
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + ∑ s' : S, (C.K s a1 a2 s').toReal * ε :=
        Finset.sum_add_distrib
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + (∑ s' : S, (C.K s a1 a2 s').toReal) * ε := by
        rw [← Finset.sum_mul]
    _ ≤ (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + 1 * ε := by
        linarith [mul_le_mul_of_nonneg_right hmass hε]
    _ = (∑ s' : S, (C.K s a1 a2 s').toReal * w s') + ε := by rw [one_mul]
end Csg.CSG
