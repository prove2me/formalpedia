-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.length_bound_under_twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:27.081362+00:00
-- url     : https://prove2.me/submissions/58a88f2e-eeeb-4499-bd84-36bebe648c68

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : LemmaB'_twist := by
  intro k lam a W b' h0 hW hl
  have hk : (0:ℚ) < (k:ℚ) + 2 := by positivity
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW (Fin.last (k+1)) (by simp [Fin.ext_iff]))
  have hb : b' ≤ W := by
    have := hW (Fin.last (k+1)) (by simp [Fin.ext_iff])
    rw [hl, abs_neg] at this
    exact le_trans (le_abs_self _) this
  rw [div_add' _ _ _ hk.ne', div_le_div_iff_of_pos_right hk, Fin.sum_univ_succ, h0]
  have : ∑ i : Fin (k+1), (lam i.succ + b') ≤ ∑ i : Fin (k+1), (W + W) := by
    apply Finset.sum_le_sum
    intro i _
    have := hW i.succ (Fin.succ_ne_zero i)
    linarith [le_trans (le_abs_self _) this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  nlinarith
end Formalism.HermitianLattices.LocalLatticeBases
