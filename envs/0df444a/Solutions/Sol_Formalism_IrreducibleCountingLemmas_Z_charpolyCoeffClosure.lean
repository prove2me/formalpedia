-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.charpolyCoeffClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:46.843948+00:00
-- url     : https://prove2.me/submissions/f4c5157e-9a43-47f8-8345-ede28f44c020

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ContinuousCoeffCharpolyRev
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_continuous_coeff_charpolyRev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : CharpolyCoeffClosure := by
  intro G _ R _ _ _ X _ n r T D hr hT hD hDT g j
  have hc : Continuous fun g => (fun x => (Matrix.charpolyRev (r x g)).coeff j) :=
    continuous_pi fun x => continuous_coeff_charpolyRev (hr x) j
  have hcl : IsClosed {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := hT.preimage hc
  have hsub : D ⊆ {g | (fun x => (Matrix.charpolyRev (r x g)).coeff j) ∈ T} := fun g hg => hDT g hg j
  have hcs := hcl.closure_subset_iff.mpr hsub
  exact hcs (by rw [hD.closure_eq]; exact Set.mem_univ g)
end Formalism.IrreducibleCountingLemmas.Z
