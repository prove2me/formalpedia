-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_Hb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:48:29.480804+00:00
-- url     : https://prove2.me/submissions/000dc981-05c0-4bba-8699-da3c0168cf76

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (u v : Fin (k + 1) → ℂ) :
    herm (Hb k) u v = (∑ i : Fin k, star (v i.castSucc) * u i.castSucc) - star (v (Fin.last k)) * u (Fin.last k) := by
  unfold herm Hb
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp [Matrix.mulVec_diagonal, Fin.castSucc_ne_last, sub_eq_add_neg]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
