-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.sec_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:12.697695+00:00
-- url     : https://prove2.me/submissions/eea952e5-1e4c-4c8b-893f-58a923cc484d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_inWb_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH

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
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec) {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (embWb k r (μsec ζ) *ᵥ z') ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') (embWb k r (μsec ζ) *ᵥ z') = herm (Hpk k r) z' z' ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') z = ζ := by
  obtain ⟨hU, hval⟩ := hsec.2 ζ hζ
  have hU' : μsec ζ ∈ UH (Hb k) := hU
  have e : embWb k r (μsec ζ) *ᵥ z' = jV k r (μsec ζ *ᵥ wbPart k r z') := by
    conv_lhs => rw [← jV_wbPart hz']
    rw [emb_mulVec_jV]
  rw [e]
  refine ⟨inWb_jV _, ?_, ?_⟩
  · rw [herm_jV, herm_UH hU']
    conv_rhs => rw [← jV_wbPart hz']
    rw [herm_jV]
  · conv_lhs => rw [← jV_wbPart hz]
    rw [herm_jV, hval]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
