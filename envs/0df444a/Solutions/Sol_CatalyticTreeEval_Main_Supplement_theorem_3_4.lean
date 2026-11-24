-- Prove2me | solution 1 for CatalyticTreeEval.Main.Supplement.theorem_3_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T21:39:06.244038+00:00
-- url     : https://prove2.me/submissions/f18ae347-50d6-4121-89fa-e1cb61336f13
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CatalyticTreeEval_Main_Supplement_UniformConstructions
import Theorems.Thm_CatalyticTreeEval_Main_Supplement_corollary_4_9

set_option autoImplicit false

namespace CatalyticTreeEval.Main.Supplement

/-- Theorem 3.4 from the input-length (second) part of Corollary 4.9, forgetting the time bound. -/
theorem theorem_3_4_of_corollary_4_9 :
    ∃ (M : Machine) (Cs : ℝ), 0 < Cs ∧
      ∀ h l : ℕ, 0 < h → 0 < l → ∀ I : Tree l h,
      Prints M I.encode (bits l I.value.val)
        (Cs * lg I.encode.length * loglog I.encode.length) := by
  obtain ⟨M, Cs, _Ct, hCs, _hCt, hM⟩ := corollary_4_9
  refine ⟨M, Cs, hCs, fun h l hh hl I => ?_⟩
  obtain ⟨t, c, hrun, hst, hout, hwb, _⟩ := (hM h l hh hl I).2
  exact ⟨t, c, hrun, hst, hout, hwb⟩

end CatalyticTreeEval.Main.Supplement

open CatalyticTreeEval.Main CatalyticTreeEval.Main.Supplement in
theorem solution :
    ∃ (M : Machine) (Cs : ℝ), 0 < Cs ∧
      ∀ h l : ℕ, 0 < h → 0 < l → ∀ I : Tree l h,
      Prints M I.encode (bits l I.value.val)
        (Cs * lg I.encode.length * loglog I.encode.length) :=
  theorem_3_4_of_corollary_4_9
