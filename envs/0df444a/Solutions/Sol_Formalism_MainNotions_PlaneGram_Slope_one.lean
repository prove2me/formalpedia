-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Slope.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:48:59.676188+00:00
-- url     : https://prove2.me/submissions/48cfcb95-fe1c-4483-8706-6f8aa5e699be

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

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
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open Formalism.MainNotions.PlaneGram.Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
namespace Formalism.MainNotions.PlaneGram.Slope
theorem _root_.solution (h1 : TotallyRealRoots 0 (fun _ => 1)) : Slope v TotallyRealRoots c (fun _ => 1) := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun _ _ => 1, ?_, ?_, ?_, ?_⟩
  · intro k
    simp
  · intro k
    exact h1
  · intro k α
    simp
  · intro α
    simp
end Formalism.MainNotions.PlaneGram.Slope
