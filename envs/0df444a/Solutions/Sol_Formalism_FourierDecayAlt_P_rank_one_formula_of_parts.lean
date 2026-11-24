-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rank_one_formula_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:50.504701+00:00
-- url     : https://prove2.me/submissions/f5962e1f-4c06-4f5f-8a64-e429cc12ddbe

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_on
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_section
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_secF_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_lint_nu
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_conc
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_nu_ne_zero

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleRankOne := by
  intro HU CWb CW KW UF RM RC HI k r z z' μsec μb μW μW' hk hz hz' hT hT' hsec hb hW hW'
  haveI := haar_sigmaFinite hW
  haveI := haar_sigmaFinite hW'
  have hsm : MeasSec (secF k r z z' μsec) := secF_meas hsec
  have hss : IsSection k r z z' (secF k r z z' μsec) := secF_section hsec
  have hsu : ∀ ζ, (secF k r z z' μsec ζ)ᴴ * Hb k * secF k r z z' μsec ζ = Hb k := secF_unit hsec
  obtain ⟨c, hc⟩ := HU k r (UWb k r) μb (nu z z' (secF k r z z' μsec) μW μW') (CWb k r) hb
    (nu_conc CWb CW UF z z' hsm hsu hW hW')
    (fun a ha => nu_left CWb CW UF HI z z' hsm hsu hk hz hz' hT hT' hss hW hW' a ha)
    (fun K hK => nu_finite KW RM z z' hsm hz hz' hT hT' hss hW hW' K hK)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact nu_ne_zero z z' hsm hW hW' (by rw [hc]; simp)
  refine ⟨c⁻¹, inv_pos.2 (pos_iff_ne_zero.2 hc0), fun f hf => ?_⟩
  have hint := lint_nu hsm z z' μW μW' f hf
  have e1 : ∫⁻ m, f m ∂(nu z z' (secF k r z z' μsec) μW μW') = (c : ℝ≥0∞) * ∫⁻ m, f m ∂μb := by
    rw [hc, lintegral_smul_measure]
    first
      | rfl
      | simp [ENNReal.smul_def]
      | simp
  have e2 : ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p, f (Phi (secF k r z z' μsec) (ζ, p)) ∂(μW.prod μW') =
      ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * embWb k r (μsec ζ) * Matrix.of p.2) ∂(μW.prod μW') := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_Om (r := r) z z'] with ζ hζ
    rcases hζ with hζ | hζ
    · congr 1
      refine lintegral_congr fun p => ?_
      show f ((Matrix.of p.1 : Mat k r)⁻¹ * embWb k r (secF k r z z' μsec ζ) * Matrix.of p.2) = _
      rw [secF_on hζ]
    · rw [hζ]
      simp
  have hcne : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  calc ∫⁻ m, f m ∂μb = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∫⁻ m, f m ∂μb) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcne ENNReal.coe_ne_top, one_mul]
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ m, f m ∂(nu z z' (secF k r z z' μsec) μW μW') := by rw [e1]
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p, f (Phi (secF k r z z' μsec) (ζ, p)) ∂(μW.prod μW') := congrArg (fun t => (c : ℝ≥0∞)⁻¹ * t) hint
    _ = _ := by rw [e2, ENNReal.coe_inv hc0]
end Formalism.FourierDecayAlt.P
