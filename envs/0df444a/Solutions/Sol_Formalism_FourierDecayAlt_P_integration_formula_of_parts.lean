-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.integration_formula_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:27:53.603801+00:00
-- url     : https://prove2.me/submissions/af9e35b3-1c40-4bc0-b256-af67b9ed4eec

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_section
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_embS_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_sgs_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_big_cell_coordinate_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_engine

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1 Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleInt := by
  intro hIter hR1 hConj hWbE hBCF UF hWF k r z z' μsec μG μW μN μW' hD
  obtain ⟨μb, hb⟩ := hWbE k r
  have hsec' := secF_section hD.sec
  have hsm := secF_meas hD.sec
  have := haar_sigmaFinite hD.haarW
  have := haar_sigmaFinite hD.haarW'
  have := haar_sigmaFinite hD.haarN
  have := haar_sigmaFinite hb
  obtain ⟨C1, hC1, h1⟩ := hIter k r μG μN μb hD.haarG hD.haarN hb
  obtain ⟨C2, hC2, h2⟩ := hR1 k r z z' (secF k r z z' μsec) μb μW μW' hD.k_pos hD.z_mem hD.z'_mem hD.T_pos hD.T'_pos
    hsec' hb hD.haarW hD.haarW'
  refine ⟨C1 * C2, mul_pos hC1 hC2, fun f hf => ?_⟩
  have h1' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = (C1 : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ,
      ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, bc1 k r c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) := h1
  have h2' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = (C2 : ℝ≥0∞) * ∫⁻ ζ : ℂ,
      ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * ∫⁻ p : Mt k r × Mt k r,
        f (mulM (mulM (invM p.1, embF k r (secF k r z z' μsec ζ)), p.2)) ∂(μW.prod μW') := h2
  have e := engine (μG := μG) (μN := μN) (μb := μb) (μW := μW) (μW' := μW') (Tz k r z) (Tz k r z') (bc1 k r) big_cell_coordinate_measurable
    (fun ζ => embF k r (secF k r z z' μsec ζ)) (embS_meas hsm) C1 C2 h1' h2'
    (fun c ζ f hf => key UF hD.haarW hD.haarW' (hConj k r z μN hD.z_mem hD.T_pos hD.haarN)
      (hConj k r z' μN hD.z'_mem hD.T'_pos hD.haarN) (bc1 k r c) _ ((UF k r).2.2 c) f hf) f hf
  rw [e]
  refine congrArg (((C1 * C2 : ℝ≥0) : ℝ≥0∞) * ·) ?_
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ q : (Fin r → ℂ) × ℂ, q.2 ∈ Om k r z z' ∨ zWeight k (Tz k r z) (Tz k r z') q.2 = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))).ae
      (ae_Om z z')
  filter_upwards [hae] with q hq
  rw [hWF k r (Tz k r z) (Tz k r z') q]
  rcases hq with h | h
  · refine congrArg (ENNReal.ofReal (cWeight k r q.1 * zWeight k (Tz k r z) (Tz k r z') q.2) * ·) ?_
    refine lintegral_congr fun p => congrArg f ?_
    have e3 : (bigCell k r q.1 (μsec q.2) : Mt k r) = mulM (bc1 k r q.1, embF k r (secF k r z z' μsec q.2)) := by
      rw [secF_on h]; exact (hBCF k r q.1 (μsec q.2)).1
    rw [sgs_eq, e3]
  · rw [h]; simp
end Formalism.FourierDecayAlt.P
