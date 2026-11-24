-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.UWset_inv_mem_UWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:38.39579+00:00
-- url     : https://prove2.me/submissions/20a8f5ae-6e14-4832-a4b1-d0518d4b41c6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWset_iff

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWb k r := by
  obtain ⟨η, hη, -, rfl⟩ := (UWset_iff hz h).1 hh
  rw [emb_inv hη]
  exact (UWb_iff _).2 ⟨η⁻¹, (UHb_inv hη).2, rfl⟩
end Formalism.FourierDecayAlt.P.TwoByOneBlock
