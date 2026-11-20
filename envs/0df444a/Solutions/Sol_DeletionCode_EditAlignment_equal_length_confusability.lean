-- Prove2me | solution 1 for DeletionCode.EditAlignment.equal_length_confusability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:44.598968+00:00
-- url     : https://prove2.me/submissions/af1cdfee-5cc9-4ffd-ad22-4c23fe335444

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_EditAlignment
import Theorems.Thm_DeletionCode_EditAlignment_Script_trans
import Theorems.Thm_DeletionCode_EditAlignment_Script_reverse
import Theorems.Thm_DeletionCode_EditAlignment_Script_length_balance
import Theorems.Thm_DeletionCode_EditAlignment_Script_surviving_subsequence
import Theorems.Thm_DeletionCode_EditAlignment_alignment_of_common_subsequence

set_option autoImplicit true
open DeletionCode DeletionCode.EditAlignment
namespace DeletionCode.EditAlignment
theorem _root_.solution (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ d, d ≤ t ∧ Alignment y z d d := by
  obtain ⟨dy, iy, hyu, hcosty⟩ := hyu
  obtain ⟨dz, iz, hzu, hcostz⟩ := hzu
  have hscript : Script y z (dy + iz) (iy + dz) := hyu.trans hzu.reverse
  have hbalance := hscript.length_balance
  have hdeletions : dy + iz ≤ t := by omega
  obtain ⟨w, hwy, hwz, hsurvive⟩ := hscript.surviving_subsequence
  refine ⟨n - w.length, by omega, ?_⟩
  simpa only [hy, hz] using alignment_of_common_subsequence hwy hwz
end DeletionCode.EditAlignment
