-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.surjective_sigmaOpensDesc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:18.80373+00:00
-- url     : https://prove2.me/submissions/f1f0d17f-95bd-4a7a-af7a-9f2b841589d9

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_sigma___sigmaOpensDesc_a310daec50eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) : Surjective (sigmaOpensDesc Y U) := by
  constructor
  intro y
  have hy : y ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨(Sigma.ι (fun i => (U i).toScheme) i).base (⟨y, hi⟩ : ↥((U i).toScheme)), ?_⟩
  exact congrArg (fun f : (U i).toScheme ⟶ Y => f.base (⟨y, hi⟩ : ↥((U i).toScheme)))
    (sigma_ι_sigmaOpensDesc Y U i)
end FunctorialResolution.EmbeddedResolution
