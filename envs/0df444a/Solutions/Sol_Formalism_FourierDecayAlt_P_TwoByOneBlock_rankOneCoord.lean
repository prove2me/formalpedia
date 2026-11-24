-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.rankOneCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:04:14.506114+00:00
-- url     : https://prove2.me/submissions/8f4ccc4b-8d75-44d7-b5d7-8b574638e83b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_wbPart_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_inWb_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWset_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_self_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sec_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mul


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
theorem _root_.solution : RankOneCoord := by
  intro k r z z' μsec _ hz hz' hT _ hsec m hm hζ
  set ζ := herm (Hpk k r) (m *ᵥ z') z with hζdef
  obtain ⟨hU, _⟩ := hsec.2 ζ hζ
  have hU' : μsec ζ ∈ UH (Hb k) := hU
  obtain ⟨s1, s2, s3⟩ := sec_vec hz hz' hsec hζ
  obtain ⟨ν, hν, rfl⟩ := (UWb_iff m).1 hm
  have e : embWb k r ν *ᵥ z' = jV k r (ν *ᵥ wbPart k r z') := by
    conv_lhs => rw [← jV_wbPart hz']
    rw [emb_mulVec_jV]
  have n1 : herm (Hpk k r) (embWb k r ν *ᵥ z') (embWb k r ν *ᵥ z') = herm (Hpk k r) z' z' := by
    rw [e, herm_jV, herm_UH hν]
    conv_rhs => rw [← jV_wbPart hz']
    rw [herm_jV]
  obtain ⟨h, hh, hv⟩ := orbit (v₁ := embWb k r ν *ᵥ z') (v₂ := embWb k r (μsec ζ) *ᵥ z') hz
    (by rw [e]; exact inWb_jV _) s1 hT.ne' (by rw [n1, s2]) (by rw [s3]) (by
      rw [n1, herm_self_eq z', ← hζdef]
      simp only [Complex.neg_re, Complex.ofReal_re]
      nlinarith)
  obtain ⟨η, hη, hηz, rfl⟩ := (UWset_iff hz h).1 hh
  have hfix : ((μsec ζ)⁻¹ * η * ν) *ᵥ wbPart k r z' = wbPart k r z' := by
    have h1 : η *ᵥ (ν *ᵥ wbPart k r z') = μsec ζ *ᵥ wbPart k r z' := by
      have h2 := congrArg (wbPart k r) hv
      rw [e, emb_mulVec_jV, wbPart_jV] at h2
      rw [h2]
      conv_lhs => rw [← jV_wbPart hz']
      rw [emb_mulVec_jV, wbPart_jV]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (UHb_inv hU').1, Matrix.one_mulVec]
  refine ⟨embWb k r η, hh, embWb k r ((μsec ζ)⁻¹ * η * ν),
    (UWset_iff hz' _).2 ⟨_, UHb_mul (UHb_mul (UHb_inv hU').2 hη) hν, hfix, rfl⟩, ?_⟩
  rw [emb_inv hη, ← emb_mul, ← emb_mul]
  congr 1
  rw [Matrix.mul_assoc (μsec ζ)⁻¹, ← Matrix.mul_assoc _ (μsec ζ)⁻¹, Matrix.mul_assoc η⁻¹,
    Matrix.mul_nonsing_inv _ (UHb_inv hU').1, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (UHb_inv hη).1, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
