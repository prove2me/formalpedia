-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.finite_coker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:02.169366+00:00
-- url     : https://prove2.me/submissions/1a0aed70-99fa-4151-82a0-d3506fd677f1

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finite_quot
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isoFinite


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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (hD : LocalDatum K R ψ) {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (hZ : IsInt R Z) (hdet : IsUnit Z.det) : Finite (coker R Z) :=
  (Formalism.DoubleCosetMeasures.P.isoFinite K R (finite_quot hD) n Z hZ hdet).1
end Formalism.FourierDecayAlt.P.A5x3
