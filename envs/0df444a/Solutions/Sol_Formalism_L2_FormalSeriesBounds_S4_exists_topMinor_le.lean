-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.exists_topMinor_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:29.819908+00:00
-- url     : https://prove2.me/submissions/443553b3-9e6c-4d04-8e56-85e24611a1f6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_le_v_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) (n : ℕ) :
    ∀ (k : ℕ) (Y : Matrix (Fin (n + k)) (Fin (n + k)) R),
      ∃ f : Fin n → Fin (n + k), StrictMono f ∧
        v (Y.submatrix (Fin.castAdd k) f).det ≤ v Y.det := by
  intro k
  induction k with
  | zero =>
    intro Y
    exact ⟨Fin.castAdd 0, Fin.strictMono_castAdd 0, le_of_eq rfl⟩
  | succ k ih =>
    intro Y
    have hexp := Matrix.det_succ_row Y (Fin.last (n + k))
    obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ
      (fun j : Fin (n + k + 1) => v (Y.submatrix (Fin.last (n + k)).succAbove j.succAbove).det)
      Finset.univ_nonempty
    have hle : v (Y.submatrix (Fin.last (n + k)).succAbove j.succAbove).det ≤ v Y.det := by
      rw [hexp]
      apply le_v_sum
      intro i _
      rw [v.map_mul]
      exact le_trans (hj i (Finset.mem_univ _)) (le_add_of_nonneg_left (hv _))
    obtain ⟨f', hf', hle'⟩ := ih (Y.submatrix (Fin.last (n + k)).succAbove j.succAbove)
    refine ⟨j.succAbove ∘ f', (Fin.strictMono_succAbove j).comp hf', le_trans (le_of_eq ?_) (le_trans hle' hle)⟩
    congr 2
    ext a b
    simp only [Matrix.submatrix_apply, Function.comp_apply, Fin.succAbove_last]
    congr 1
end Formalism.L2.FormalSeriesBounds.S4
