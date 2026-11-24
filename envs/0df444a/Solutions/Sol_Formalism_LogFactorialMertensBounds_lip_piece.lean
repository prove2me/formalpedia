-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.lip_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:25.718821+00:00
-- url     : https://prove2.me/submissions/9e97113b-8352-40e3-8b8b-3c81fb94b657

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_Gz_eq_P
import Theorems.Thm_Formalism_LogFactorialMertensBounds_hasDerivAt_P
import Theorems.Thm_Formalism_LogFactorialMertensBounds_deriv_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) (x y : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1)
    (hy1 : (k:ℝ) ≤ y) (hy1' : 1 / 2 ≤ y) (hy2 : y ≤ k + 1) :
    |Gz y - Gz x| ≤ K0 * |y - x| := by
  have hs : Convex ℝ (Set.Icc (max (k:ℝ) (1 / 2)) (k + 1)) := convex_Icc _ _
  have hder : ∀ t ∈ Set.Icc (max (k:ℝ) (1 / 2)) (k + 1),
      HasDerivWithinAt (P k) (A k - Real.log t + Real.eulerMascheroniConstant)
        (Set.Icc (max (k:ℝ) (1 / 2)) (k + 1)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right (k:ℝ) (1 / 2)) ht.1)
    exact (hasDerivAt_P k htpos).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Icc (max (k:ℝ) (1 / 2)) (k + 1),
      ‖A k - Real.log t + Real.eulerMascheroniConstant‖ ≤ K0 := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact deriv_bound k t (le_trans (le_max_left _ _) ht.1) (le_trans (le_max_right _ _) ht.1) ht.2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb hs
    ⟨max_le hx1 hx1', hx2⟩ ⟨max_le hy1 hy1', hy2⟩
  rw [Gz_eq_P k x hx1 hx2, Gz_eq_P k y hy1 hy2]
  simpa [Real.norm_eq_abs] using h
end Formalism.LogFactorialMertensBounds
