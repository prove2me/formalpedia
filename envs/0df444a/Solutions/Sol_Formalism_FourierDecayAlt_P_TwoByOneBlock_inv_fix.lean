-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.inv_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:48.43153+00:00
-- url     : https://prove2.me/submissions/e0d2fb84-0dd2-4a6d-8dac-bed1ee2a47b7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : a ∈ UH (Hb k)) {x : Fin (k + 1) → ℂ}
    (hx : a *ᵥ x = x) : a⁻¹ *ᵥ x = x := by
  conv_lhs => rw [← hx]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (UHb_inv ha).1, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
