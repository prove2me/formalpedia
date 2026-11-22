-- Prove2me | solution 1 for Formalism.GM.TM.takeD_total_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:15.188801+00:00
-- url     : https://prove2.me/submissions/20866ff3-efee-4f3d-875a-d78aab6b9e57

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {N : ℕ}
namespace Formalism.GM.TM
theorem _root_.solution (LL : Letters N) (T : TieData) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (LL.takeD (T.pos i + 1)).total = T.S LL i := by
  unfold Letters.total TieData.S Letters.takeD
  dsimp only
  let g : ℕ → ℕ := fun a => if h : a < N then (if a ≤ T.pos i then LL.deg ⟨a, h⟩ else 0) else 0
  have e1 : (∑ a : Fin (T.pos i + 1), if h : (a : ℕ) < N then LL.deg ⟨a, h⟩ else 0) = ∑ a ∈ range (T.pos i + 1), g a := by
    rw [Fin.sum_univ_eq_sum_range (fun a => if h : a < N then LL.deg ⟨a, h⟩ else 0)]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [mem_range] at ha
    simp only [g]
    split_ifs <;> first | rfl | omega
  have e2 : (∑ a : Fin N, if (a : ℕ) ≤ T.pos i then LL.deg a else 0) = ∑ a ∈ range N, g a := by
    rw [← Fin.sum_univ_eq_sum_range g N]
    apply Finset.sum_congr rfl
    intro a _
    simp only [g, dif_pos a.isLt]
  rw [e1, e2, ← Finset.sum_range_add_sum_Ico g (by omega : T.pos i + 1 ≤ N)]
  have : ∑ a ∈ Ico (T.pos i + 1) N, g a = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [mem_Ico] at ha
    simp only [g]
    split_ifs <;> first | rfl | omega
  omega
end Formalism.GM.TM
