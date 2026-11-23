-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.pairV_isUniU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:27.509217+00:00
-- url     : https://prove2.me/submissions/9c9e4593-59fa-4c3d-9abe-ffe44cfe1337

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairV_apply

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
    (hg : ∀ j, s.castSucc < j → ∀ b, b < j → h j b = 0) (t : k) : IsUniU (pairV h s l t) := by
  have hls : l.castSucc < s.succ :=
    lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.2 hl) ((Fin.castSucc_lt_succ : s.castSucc < s.succ))
  have hsl : h s.succ l.castSucc = 0 := hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) l.castSucc hls
  refine ⟨fun i => ?_, fun i j hji => ?_⟩
  · rw [pairV_apply, Matrix.one_apply_eq]
    by_cases hi : i = l.castSucc
    · subst hi
      rw [hsl]
      ring
    · rw [if_neg hi]
      ring
  · rw [pairV_apply, Matrix.one_apply_ne hji.ne']
    by_cases hi : i = l.castSucc
    · subst hi
      rw [hg s.succ ((Fin.castSucc_lt_succ : s.castSucc < s.succ)) j (lt_trans hji hls)]
      ring
    · rw [if_neg hi]
      ring
end Formalism.EigenvalueLevelCeiling
