-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.assembleIter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:41.136717+00:00
-- url     : https://prove2.me/submissions/0cc55d62-507e-43de-96ff-9a696eb0b2ed

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_iter_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_iter_base

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
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution : AssembleIter := by
  intro hO HU _ hL _ hCN hCb hG hNe hWb hNR hNB hC _ _ _ k r
  induction r with
  | zero => exact iter_base HU hCb hNB k
  | succ r' ih =>
    have h := iter_step hO HU hL hCN hCb hG hNe hWb hNR hC k r' ih
    rw [Nat.add_comm 1 r'] at h
    exact h
end Formalism.FourierDecayAlt.P.LongWeylElement
