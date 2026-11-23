-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.det_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:04.235803+00:00
-- url     : https://prove2.me/submissions/30a8b13e-21cb-421b-b5fd-4c827e1a0a1a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution {k n : ℕ} {Z : Matrix (Fin n) (Fin n) K} (hZ : IsInt R Z)
    (r c : Fin k → Fin n) : (Z.submatrix r c).det ∈ R := by
  let M : Matrix (Fin k) (Fin k) R := fun a b => ⟨Z (r a) (c b), hZ _ _⟩
  have h : Z.submatrix r c = R.subtype.mapMatrix M := by ext a b; rfl
  rw [h, ← RingHom.map_det]
  exact M.det.2
end Formalism.FourierDecayAlt.P.A5x7
