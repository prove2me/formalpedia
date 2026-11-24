-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:51:01.277992+00:00
-- url     : https://prove2.me/submissions/ae1c2b94-dcba-4c34-9457-b9cf426eeb38

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_det_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_det_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_det_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (v : Fin n → ℝ) (b : ℕ) :
    ∑ s ∈ powersetCard b (univ : Finset (Fin n)), qk_D (s.piecewise (fun i => v i - 1) v) =
      (n.choose b : ℝ) * qk_D v := by
  have h1 := qk_det_expand (fun i => (C (v i) : ℝ[X])) (fun i => (C (v i) : ℝ[X]) - 1) X
  rw [qk_det_shift, qk_det_C] at h1
  have h2 : ∀ s : Finset (Fin n), (Matrix.vandermonde (s.piecewise (fun i => (C (v i) : ℝ[X]) - 1)
      (fun i => (C (v i) : ℝ[X])))).det = C (qk_D (s.piecewise (fun i => v i - 1) v)) := by
    intro s
    rw [← qk_det_C]
    congr 2
    funext i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [h2] at h1
  have h3 := congrArg (fun q : ℝ[X] => q.coeff b) h1
  simp only [finsetSum_coeff] at h3
  rw [coeff_C_mul, coeff_one_add_X_pow, mul_comm] at h3
  rw [h3, ← sum_filter_add_sum_filter_not univ (fun s : Finset (Fin n) => s.card = b)]
  have h4 : ∑ s ∈ univ.filter (fun s : Finset (Fin n) => ¬ s.card = b),
      ((X : ℝ[X]) ^ s.card * C (qk_D (s.piecewise (fun i => v i - 1) v))).coeff b = 0 := by
    refine sum_eq_zero fun s hs => ?_
    rw [mul_comm, coeff_C_mul_X_pow, if_neg (fun h => (mem_filter.1 hs).2 h.symm)]
  rw [h4, add_zero]
  have h5 : powersetCard b (univ : Finset (Fin n)) = univ.filter (fun s : Finset (Fin n) => s.card = b) := by
    ext s
    simp [mem_powersetCard]
  rw [h5]
  refine sum_congr rfl fun s hs => ?_
  rw [mul_comm, coeff_C_mul_X_pow, if_pos (mem_filter.1 hs).2.symm]
end Formalism.InvariantFactorPaths.ColumnFamilies
