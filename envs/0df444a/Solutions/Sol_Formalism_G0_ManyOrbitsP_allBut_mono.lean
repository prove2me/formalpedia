-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.allBut_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:23.907982+00:00
-- url     : https://prove2.me/submissions/98b9ceb7-54fe-4a98-a71d-d248eaf86ba7

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution {π : R} {M P : Submodule R X} {g g' E E' : ℕ} (h : AllButLE π M P g E)
    (hg : g ≤ g') (hE : E ≤ E') : AllButLE π M P g' E' := by
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C, hCM, hcard.trans hg, fun x hx => ?_⟩
  have := Submodule.smul_mem _ (π ^ (E' - E)) (hC x hx)
  rwa [smul_smul, ← pow_add, Nat.sub_add_cancel hE] at this
end Formalism.G0.ManyOrbitsP
