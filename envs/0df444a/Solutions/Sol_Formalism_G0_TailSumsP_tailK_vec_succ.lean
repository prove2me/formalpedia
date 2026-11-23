-- Prove2me | solution 1 for Formalism.G0.TailSumsP.tailK_vec_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:26.739921+00:00
-- url     : https://prove2.me/submissions/72920d4e-cf4c-4269-aa51-6ec96f70b886

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP
namespace Formalism.G0.TailSumsP
theorem _root_.solution {K : ℕ} {α α' : Fin K → ℕ} {B : ℕ} (h : VecStep α α' B) (u : ℕ) :
    tailK α' (u + 1) ≤ tailK α u := by
  obtain ⟨-, h2, -⟩ := h
  cases K with
  | zero => simp [tailK]
  | succ k =>
    unfold tailK
    rw [Fin.sum_univ_succ,
      Fin.sum_univ_castSucc (f := fun l : Fin (k + 1) => if u ≤ l.val then α l else 0)]
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Nat.add_le_add_iff_right,
      Nat.le_zero, Nat.add_one_ne_zero, if_false, zero_add]
    refine le_trans ?_ (Nat.le_add_right _ _)
    apply Finset.sum_le_sum
    intro i _
    by_cases hu : u ≤ i.val
    · rw [if_pos (by omega), if_pos hu]
      have hh : i.castSucc.val + 1 < k + 1 := by simp
      have e : (⟨i.castSucc.val + 1, hh⟩ : Fin (k + 1)) = i.succ := Fin.ext (by simp)
      have := h2 i.castSucc hh
      rw [e] at this
      exact this
    · rw [if_neg (by omega), if_neg hu]
end Formalism.G0.TailSumsP
