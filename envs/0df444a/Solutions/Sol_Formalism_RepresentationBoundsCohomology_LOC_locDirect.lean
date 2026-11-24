-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.locDirect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:36:47.754324+00:00
-- url     : https://prove2.me/submissions/e045c049-7d46-4459-a8ec-c9a92c1529e8

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatLocDirect.{u} := by
  intro O A HV _ _ _ _ _ q HfV P ℓ e' hF hL y hy
  obtain ⟨x, hx, hxy⟩ := hL y hy
  refine ⟨P.p2 (P.jL x), hF hx, ?_⟩
  rw [← P.comm x, hxy, map_smul]
end Formalism.RepresentationBoundsCohomology.LOC
