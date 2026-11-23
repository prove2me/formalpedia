-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.rowFun_kills
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:27.388688+00:00
-- url     : https://prove2.me/submissions/1931b4d4-0ffe-4dd1-857b-8c764d170248

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_rowFun_apply

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
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (a : Fin n) :
    latZ R Z ≤ LinearMap.ker (rowFun R Z a) := by
  intro v hv
  obtain ⟨y, hy⟩ := (Formalism.DoubleCosetMeasures.P.mem_latZ R Z v).1 hv
  rw [LinearMap.mem_ker, rowFun_apply, ← hy, mulVec_mulVec, Matrix.nonsing_inv_mul Z hZ,
    one_mulVec, mk_eq_zero, Formalism.DoubleCosetMeasures.P.coeLin_apply]
  exact (y a).2
end Formalism.FourierDecayAlt.P.A5x3
