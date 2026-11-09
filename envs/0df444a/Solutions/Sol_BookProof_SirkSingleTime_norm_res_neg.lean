-- Prove2me | solution 1 for BookProof.SirkSingleTime.norm_res_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T20:03:01.559038+00:00
-- url     : https://prove2.me/submissions/e8699991-d612-415f-9133-b06b03b75b9e

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.norm_res_neg
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterStoneResolvent
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (T : UnboundedSelfAdjoint E) {l : ℝ} (hl : l ≠ 0) (y : E) :
    ‖((T.res (-l) y : T.domain) : E)‖ = ‖((T.res l y : T.domain) : E)‖ := by

  have hl' : -l ≠ 0 := neg_ne_zero.mpr hl
  have h1 : ⟪((T.res l y : T.domain) : E), ((T.res l y : T.domain) : E)⟫_ℂ
      = ⟪y, ((T.res (-l) (((T.res l y : T.domain) : E)) : T.domain) : E)⟫_ℂ :=
    T.inner_res hl y ((T.res l y : T.domain) : E)
  have h2 : ⟪((T.res (-l) y : T.domain) : E), ((T.res (-l) y : T.domain) : E)⟫_ℂ
      = ⟪y, ((T.res l (((T.res (-l) y : T.domain) : E)) : T.domain) : E)⟫_ℂ := by
    simpa using T.inner_res hl' y ((T.res (-l) y : T.domain) : E)
  have hcomm : ((T.res (-l) (((T.res l y : T.domain) : E)) : T.domain) : E)
      = ((T.res l (((T.res (-l) y : T.domain) : E)) : T.domain) : E) := T.res_comm hl' hl y
  have heq : ⟪((T.res (-l) y : T.domain) : E), ((T.res (-l) y : T.domain) : E)⟫_ℂ
      = ⟪((T.res l y : T.domain) : E), ((T.res l y : T.domain) : E)⟫_ℂ := by
    rw [h2, h1, hcomm]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at heq
  have hre : ‖((T.res (-l) y : T.domain) : E)‖ ^ 2 = ‖((T.res l y : T.domain) : E)‖ ^ 2 := by
    exact_mod_cast heq
  rw [← Real.sqrt_sq (norm_nonneg (((T.res (-l) y : T.domain) : E))),
    ← Real.sqrt_sq (norm_nonneg (((T.res l y : T.domain) : E))), hre]
