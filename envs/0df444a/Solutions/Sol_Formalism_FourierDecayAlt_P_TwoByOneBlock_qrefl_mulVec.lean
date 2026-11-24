-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.qrefl_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:29:47.363291+00:00
-- url     : https://prove2.me/submissions/4e8772e3-3814-44f9-8e56-a1ae61a36ac2

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (c : ℂ) (x : Fin m → ℂ) :
    qrefl H d c *ᵥ x = x + (c * herm H x d) • d := by
  have h1 : Matrix.vecMulVec d (star d ᵥ* H) *ᵥ x = herm H x d • d := by
    unfold herm
    rw [Matrix.dotProduct_mulVec]
    ext i
    simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold qrefl
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, h1, smul_smul]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
