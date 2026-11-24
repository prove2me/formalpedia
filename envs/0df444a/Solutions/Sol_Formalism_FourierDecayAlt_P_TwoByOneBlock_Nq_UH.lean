-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.Nq_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:27:43.742563+00:00
-- url     : https://prove2.me/submissions/bbce09e1-43c5-4292-a383-be52baee5da7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_Hb_self

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
theorem _root_.solution {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) (u : Fin (k + 1) → ℂ) :
    Nq k (μ *ᵥ u) = Nq k u := by
  have h := herm_UH hμ u u
  rw [herm_Hb_self, herm_Hb_self] at h
  exact_mod_cast neg_injective h
end Formalism.FourierDecayAlt.P.TwoByOneBlock
