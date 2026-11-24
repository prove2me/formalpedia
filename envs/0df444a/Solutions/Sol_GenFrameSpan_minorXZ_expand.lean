-- Prove2me | solution 1 for GenFrameSpan.minorXZ_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:19.120805+00:00
-- url     : https://prove2.me/submissions/b4208d69-ecea-4c64-9656-0f4897a66e4e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_GenFrameSpan_det_mul_rect


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
namespace GenFrameSpan
theorem _root_.solution (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    minorXZ N0 N1 s p I = ∑ f : Fin p → Fin N0,
      rename (Sum.inl : _ → XZ Lt N0 N1) (Dm s p f) *
        rename (Sum.inr : _ → XZ Lt N0 N1) (Zm s p I f) := by
  let A : Matrix (Fin p) (Fin N0) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun i a => X (Sum.inl (s, (i : ℕ), a))
  let B : Matrix (Fin N0) (Fin p) (MvPolynomial (XZ Lt N0 N1) ℤ) :=
    Matrix.of fun a k => X (Sum.inr (s, a, I k))
  have hAB : minorXZ N0 N1 s p I = (A * B).det := by
    unfold minorXZ
    congr 1
  rw [hAB, det_mul_rect]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [mul_comm]
  congr 1
  · rw [Dm, AlgHom.map_det]
    congr 1
    ext i k
    simp [A, Xm, AlgHom.mapMatrix_apply, rename_X]
  · simp [Zm, B, map_prod, rename_X]
end GenFrameSpan
