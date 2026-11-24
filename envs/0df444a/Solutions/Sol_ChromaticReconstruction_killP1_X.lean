-- Prove2me | solution 1 for ChromaticReconstruction.killP1_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:24.800982+00:00
-- url     : https://prove2.me/submissions/686e8a7c-5602-45c4-94d6-f99dc47d7e03

import Definitions.Def_RequestProject_Components
import Definitions.Def_RequestProject_PhiFormula

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (r : ℕ) : killP1 (X r) = if r = 1 then 0 else X r := by
  simp [killP1]
end ChromaticReconstruction
