-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:06.778809+00:00
-- url     : https://prove2.me/submissions/31fb8988-1b3d-45c8-a8c0-d0f12aeb4283

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hb_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWset_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_self_eq

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
theorem _root_.solution {z v₁ v₂ : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hv₁ : inWb k r v₁) (hv₂ : inWb k r v₂)
    (hT : Tz k r z ≠ 0) (h12 : herm (Hpk k r) v₁ v₁ = herm (Hpk k r) v₂ v₂)
    (hζ : herm (Hpk k r) v₁ z = herm (Hpk k r) v₂ z)
    (hne : (herm (Hpk k r) v₁ v₁).re * Tz k r z + Complex.normSq (herm (Hpk k r) v₁ z) ≠ 0) :
    ∃ h ∈ UWset k r z, h *ᵥ v₁ = v₂ := by
  have hzz := herm_self_eq z
  rw [← jV_wbPart hz] at hzz hζ hne
  rw [← jV_wbPart hv₁] at h12 hζ hne
  rw [← jV_wbPart hv₂] at h12 hζ
  simp only [herm_jV] at hzz h12 hζ hne
  rw [jV_wbPart hz] at hzz hne
  obtain ⟨g, hg, hgz, hgv⟩ := trans_fix (Hb k) Hb_herm (wbPart k r z) (wbPart k r v₁) (wbPart k r v₂) (Tz k r z) hT
    hzz h12 hζ hne
  refine ⟨embWb k r g, (UWset_iff hz _).2 ⟨g, hg, hgz, rfl⟩, ?_⟩
  rw [← jV_wbPart hv₁, emb_mulVec_jV, hgv, jV_wbPart hv₂]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
