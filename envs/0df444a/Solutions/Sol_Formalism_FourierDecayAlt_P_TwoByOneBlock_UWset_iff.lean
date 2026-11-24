-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.UWset_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:26:50.480314+00:00
-- url     : https://prove2.me/submissions/45f3274e-430b-4480-b23f-867c4e63a5d0

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_wbPart_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mem_UWb
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff

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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mat k r) :
    g ∈ UWset k r z ↔ ∃ μ ∈ UH (Hb k), μ *ᵥ wbPart k r z = wbPart k r z ∧ g = embWb k r μ := by
  constructor
  · rintro ⟨hg, hfix, hgz⟩
    obtain ⟨μ, hμ, rfl⟩ := (UWb_iff g).1 ⟨hg, hfix⟩
    refine ⟨μ, hμ, ?_, rfl⟩
    rw [← jV_wbPart hz, emb_mulVec_jV] at hgz
    have := congrArg (wbPart k r) hgz
    rwa [wbPart_jV, wbPart_jV] at this
  · rintro ⟨μ, hμ, hfz, rfl⟩
    obtain ⟨h1, h2⟩ := emb_mem_UWb (r := r) hμ
    refine ⟨h1, h2, ?_⟩
    rw [← jV_wbPart hz, emb_mulVec_jV, hfz]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
