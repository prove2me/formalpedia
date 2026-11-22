-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.psi_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:27.329795+00:00
-- url     : https://prove2.me/submissions/99e57dd7-126b-4fe5-a63a-bcaedccdc3e8

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (v : P) : Function.Injective (psi (ι := ι) v) := by
  intro z z' h
  funext k
  have h0 := congrArg (fun w => w (v, k, 0)) h
  have h1 := congrArg (fun w => w (v, k, 1)) h
  exact Complex.ext (by simpa [psi_apply] using h0) (by simpa [psi_apply] using h1)
end Formalism.HN.PlaceDecomposition
