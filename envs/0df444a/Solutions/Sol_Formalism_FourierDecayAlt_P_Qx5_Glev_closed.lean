-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.Glev_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:48:55.730542+00:00
-- url     : https://prove2.me/submissions/c2adcee0-6336-4d5f-9a4a-3693e3f5c675

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_GV_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Qx2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have h : Glev k r i = UH (Hpk k r) ∩ ⋂ a : Fin r, {g : Mx k r | a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    ext g
    simp [Glev]
  rw [h]
  refine IsClosed.inter B5.GV_closed (isClosed_iInter fun a => ?_)
  by_cases ha : a.val < i.val
  · have : {g : Mx k r | a.val < i.val →
        g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} =
        {g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
      ext g
      simp [ha]
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  · have : {g : Mx k r | a.val < i.val →
        g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} = Set.univ := by
      ext g
      simp [ha]
    rw [this]
    exact isClosed_univ
end Formalism.FourierDecayAlt.P.Qx5
