-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.measurableSet_glueMap_DomR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:41.46778+00:00
-- url     : https://prove2.me/submissions/9a5b9c48-3621-43d5-8aef-c29804bb3eb8

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableOfContinuousOnZero
import Theorems.Thm_Formalism_FourierDecayAlt_P5_glueMap_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P5_DomR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_Glev_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (c : Fin r → ℂ) :
    MeasurableSet (glueMap (k := k) c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((P.Qx5.isOpen_OpR k r z z').preimage (glueMap_continuous c)).measurableSet.inter
    (((P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage (glueMap_continuous c)).measurableSet
end Formalism.FourierDecayAlt.P5
