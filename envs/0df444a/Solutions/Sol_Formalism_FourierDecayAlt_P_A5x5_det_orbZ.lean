-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x5.det_orbZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:32.194384+00:00
-- url     : https://prove2.me/submissions/f9e21939-64da-4e70-8338-4c307f2e9190

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
variable {K : Type} [CommRing K] {R : Subring K}
namespace Formalism.FourierDecayAlt.P.A5x5
theorem _root_.solution (w : Point K) (p : lowW K w.1 w.2 × upUniG K w.1.sum) :
    (orbZ w p).det = (pt w.1 w.2).det := by
  obtain ⟨h1, -⟩ := p.1.2
  have h2 : IsUpUni ((p.2 : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := p.2.2
  unfold orbZ
  rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det _ h1, isUpUni_det _ h2, one_mul, mul_one]
end Formalism.FourierDecayAlt.P.A5x5
