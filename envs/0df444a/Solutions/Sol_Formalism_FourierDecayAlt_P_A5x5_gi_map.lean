-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.gi_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:03.420804+00:00
-- url     : https://prove2.me/submissions/0986bd45-3fcc-4d58-af18-414252ddc684

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
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution {f : V →+ W} (hf : Function.Injective f) (A B : AddSubgroup V) :
    gi (A.map f) (B.map f) = gi A B := by
  unfold gi
  rw [← AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_comap,
    AddSubgroup.comap_map_eq_self_of_injective hf, AddSubgroup.comap_map_eq_self_of_injective hf]
end Formalism.FourierDecayAlt.P.A5x5
