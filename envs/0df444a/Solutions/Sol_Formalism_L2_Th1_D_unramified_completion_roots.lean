-- Prove2me | solution 1 for Formalism.L2.Th1.D.unramified_completion_roots
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:43.98299+00:00
-- url     : https://prove2.me/submissions/fe20f945-937b-4216-bc31-8435c89c4698

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded

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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open UnramifiedCompletion
namespace Formalism.L2.Th1.D
theorem _root_.solution : KurRoots := by
  intro l hl n hn hln
  have : NeZero (n : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] n
  have hmem : z ∈ MaximalUnramifiedExtension l :=
    Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hln, hz.pow_eq_one⟩)
  refine ⟨⟨z, hmem⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := (MaximalUnramifiedExtension l).subtype) hz Subtype.val_injective
end Formalism.L2.Th1.D
