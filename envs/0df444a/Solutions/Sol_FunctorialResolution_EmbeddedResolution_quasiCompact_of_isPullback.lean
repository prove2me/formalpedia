-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.quasiCompact_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:18.510124+00:00
-- url     : https://prove2.me/submissions/5056522f-f2ab-4f65-a2c6-6de894170a47

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h] :
    QuasiCompact h' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) H ‹QuasiCompact h›
end FunctorialResolution.EmbeddedResolution
