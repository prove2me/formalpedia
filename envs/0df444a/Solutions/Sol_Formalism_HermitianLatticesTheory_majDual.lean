-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:35.22389+00:00
-- url     : https://prove2.me/submissions/5895c7ab-9bce-48cb-bec9-e5b85747772e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_inner
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_tdual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_unimod
import Theorems.Thm_Formalism_HermitianLatticesTheory_majDual_zdual
import Theorems.Thm_Formalism_HermitianLatticesTheory_majLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : MajDual := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ h b X _ hst hX
  refine ⟨majDual_inner h b X hst hX, fun L hL => ?_⟩
  obtain ⟨hD, hS⟩ := majLattice K V ι b X (fun v => (hX v).1) L hL
  have hZ : IsZLattice ℝ (zmap (realize b X) L) := ⟨hS⟩
  refine ⟨⟨hD, hZ⟩, fun w => ?_, fun y => majDual_tdual h L y, fun hU y => majDual_unimod h L hU y⟩
  exact majDual_zdual h b X hst hX L w
end Formalism.HermitianLatticesTheory
