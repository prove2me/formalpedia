-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lev_out_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:31.307728+00:00
-- url     : https://prove2.me/submissions/189c1c79-0215-4e5d-be23-128a04f8a7fd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_n
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_n


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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  have hq' : ¬ mid k r' q := by
    show ¬ (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1)
    omega
  by_cases hp : mid k r' p
  · rw [lev_mn k r' g p q hp hq', if_neg]
    rintro rfl
    exact hq' hp
  · exact lev_n k r' g p q hp
end Formalism.FourierDecayAlt.P.LongWeylElement
