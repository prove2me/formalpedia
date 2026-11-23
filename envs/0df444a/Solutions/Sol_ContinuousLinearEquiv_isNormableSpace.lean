-- Prove2me | solution 1 for ContinuousLinearEquiv.isNormableSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:00:28.254794+00:00
-- url     : https://prove2.me/submissions/9fb272a6-e583-4550-b306-d9ccd6949202

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_ImportCompatibility_Normability
import Theorems.Thm_Topology_IsInducing_isNormableSpace

set_option autoImplicit true
open Topology
variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
namespace ContinuousLinearEquiv
theorem _root_.solution [IsNormableSpace 𝕜 F]
    [TopologicalSpace E] (f : E ≃L[𝕜] F) : IsNormableSpace 𝕜 E :=
  f.toHomeomorph.isInducing.isNormableSpace
end ContinuousLinearEquiv
