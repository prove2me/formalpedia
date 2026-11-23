-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.pairU_isUniU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:27.291889+00:00
-- url     : https://prove2.me/submissions/610a1a4a-034a-480b-823c-013f9e1d468c

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairU_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (hl : l ≤ s)
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairU h s l t) := by
  have hls : l.castSucc < s.succ :=
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))
  have hsl : h s.succ l.castSucc = 0 := hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [pairU_apply, Matrix.one_apply_eq]
    by_cases hi : i = s.succ
    · subst hi
      rw [hsl]
      ring
    · rw [if_neg hi]
      ring
  · rw [pairU_apply, Matrix.one_apply_ne hji.ne']
    by_cases hj : j = s.succ
    · subst hj
      rw [hg i (lt_trans ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) hji) l.castSucc (lt_trans hls hji)]
      ring
    · rw [if_neg hj]
      ring
end Formalism.EigenvalueLevelCeiling
