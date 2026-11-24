-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.image_Icc_neg_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:28.051364+00:00
-- url     : https://prove2.me/submissions/e75c9f28-7f38-45be-b7fe-699c2da2e837

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution (h x y : ℤ) :
    (Finset.Icc x y).image (fun u => h - u) = Finset.Icc (h - y) (h - x) := by
  ext z
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨h - z, ⟨by omega, by omega⟩, by omega⟩
end Formalism.CohomologicalDescent.WorkedExample
