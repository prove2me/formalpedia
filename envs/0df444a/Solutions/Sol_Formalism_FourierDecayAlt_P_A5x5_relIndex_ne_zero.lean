-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.relIndex_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:38:57.672458+00:00
-- url     : https://prove2.me/submissions/79e8b7eb-8358-426f-906c-448a1fa1975d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {V W : Type} [AddCommGroup V] [AddCommGroup W]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {U A : AddSubgroup V} (hU : IsOpen (U : Set V))
    (hA : IsCompact (A : Set V)) : U.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have ho : IsOpen ((U.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hU.preimage continuous_subtype_val
  haveI := AddSubgroup.quotient_finite_of_isOpen (U.addSubgroupOf A) ho
  exact AddSubgroup.index_ne_zero_of_finite
end Formalism.FourierDecayAlt.P.A5x5
