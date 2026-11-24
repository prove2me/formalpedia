-- Prove2me | solution 1 for Formalism.IndefR.Eqv.md_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.867316+00:00
-- url     : https://prove2.me/submissions/54366dc5-4634-4f82-a589-f1ed1d277360

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_NormIterFderivApplyLe
import Theorems.Thm_Formalism_IndefR_Eqv_contDiff_fderiv_apply
import Theorems.Thm_Formalism_IndefR_Eqv_md_succ_sub
import Theorems.Thm_Formalism_IndefR_Eqv_norm_iter_fderiv_apply_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
open Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Formalism.IndefR.Eqv
theorem _root_.solution : ∀ (n : ℕ) (φ : V → ℂ), ContDiff ℝ ∞ φ → ∀ (v : Fin n → V) (h : ℝ), 0 < h → ∀ (b : V) (M : ℝ),
    (∀ y, ‖y - b‖ ≤ h * ∑ i, ‖v i‖ → ‖iteratedFDeriv ℝ n φ y‖ ≤ M) → ‖md φ n v h b‖ ≤ M * ∏ i, ‖v i‖
  | 0, φ, hφ, v, h, hh, b, M, hM => by
    simp only [md, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    have := hM b (by simp)
    rwa [norm_iteratedFDeriv_zero] at this
  | n + 1, φ, hφ, v, h, hh, b, M, hM => by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM b (by simp; positivity))
    have key := md_succ_sub φ hφ n v hh b 0 (M * ‖v 0‖ * ∏ i, ‖Fin.tail v i‖) fun s hs => by
      rw [sub_zero]
      refine solution n (fun y => fderiv ℝ φ y (v 0)) (contDiff_fderiv_apply hφ (v 0)) (Fin.tail v) h hh
        (b + s • v 0) (M * ‖v 0‖) fun y hy => ?_
      refine (norm_iter_fderiv_apply_le hφ n (v 0) y).trans (mul_le_mul_of_nonneg_right (hM y ?_) (norm_nonneg _))
      calc ‖y - b‖ = ‖(y - (b + s • v 0)) + s • v 0‖ := by congr 1; abel
        _ ≤ ‖y - (b + s • v 0)‖ + s * ‖v 0‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg hs.1]
        _ ≤ h * ∑ i, ‖Fin.tail v i‖ + h * ‖v 0‖ := add_le_add hy (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _))
        _ = h * ∑ i, ‖v i‖ := by
          rw [Fin.sum_univ_succ]
          show h * ∑ i : Fin n, ‖v i.succ‖ + h * ‖v 0‖ = h * (‖v 0‖ + ∑ i : Fin n, ‖v i.succ‖)
          ring
    rw [sub_zero] at key
    refine key.trans (le_of_eq ?_)
    rw [Fin.prod_univ_succ]
    show M * ‖v 0‖ * ∏ i : Fin n, ‖v i.succ‖ = M * (‖v 0‖ * ∏ i : Fin n, ‖v i.succ‖)
    ring
end Formalism.IndefR.Eqv
