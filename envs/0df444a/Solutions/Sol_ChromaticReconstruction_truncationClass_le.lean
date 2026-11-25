-- Prove2me | solution 1 for ChromaticReconstruction.truncationClass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:55:06.818786+00:00
-- url     : https://prove2.me/submissions/19dfd54b-3b28-4adf-b3a8-f25880e8417f

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
import Theorems.Thm_ChromaticReconstruction_compCount_le_pow

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {k t : ℕ} (T : TreeClass k)
    (μ : {μ : Nat.Partition k // k - t ≤ Multiset.card μ.parts}) :
    truncationClass k t T μ ≤ k ^ t := by
  induction T using Quotient.inductionOn with
  | h S => exact compCount_le_pow S.2 μ.2
end ChromaticReconstruction
