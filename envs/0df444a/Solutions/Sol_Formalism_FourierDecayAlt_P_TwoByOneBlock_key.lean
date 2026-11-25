-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:24.913043+00:00
-- url     : https://prove2.me/submissions/d322ebaa-d404-43c5-9135-c77d0141dada

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_inWb_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_self_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sec_vec
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_Hb_self
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_conc_b7269f632f6d
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock__b_push_ea8e063f042e
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_meas
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoByOneBlock_act_meas__8cead913ce31
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_ae_weight
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_avg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_avg_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_Hb_meas

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
theorem _root_.solution (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {μW : Measure (Mt k r)} [SFinite μW] (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) (hW : IsHaarOn (UWset k r z) μW)
    (hf : AEMeasurable (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z'))
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      c • (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
        (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z')) = (μW Set.univ) • σV k r (Tz k r z') := by
  have hzz : herm (Hb k) (wbPart k r z) (wbPart k r z) = -((Tz k r z : ℝ) : ℂ) := by
    rw [← herm_jV (r := r), jV_wbPart hz, herm_self_eq]
  obtain ⟨c, hc0, hc1, hpush⟩ := σb_push hk hT hT' (wbPart k r z) hzz
  refine ⟨c, hc0, hc1, ?_⟩
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hFf : AEMeasurable (fun p : ℂ × Mt k r => F (act p.2 (embWb k r (μsec p.1) *ᵥ z')))
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW) :=
    hF.comp_aemeasurable hf
  have hΨm := hFf.lintegral_prod_right'
  rw [lintegral_smul_measure, lintegral_map' hF.aemeasurable hf, lintegral_prod _ hFf, smul_eq_mul,
    lintegral_smul_measure, smul_eq_mul, ← avg hz hW _ hF]
  have hGm : Measurable (fun v => ∫⁻ h, F (act h v) ∂μW) :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => F (act p.2 p.1)) (hF.comp act_meas')
  unfold σV
  rw [lintegral_map hGm jV_meas]
  have hπm := herm_Hb_meas (wbPart k r z)
  have hgg : ∀ᵐ u ∂σb k (Tz k r z'), Tz k r z * Tz k r z' < Complex.normSq (herm (Hb k) u (wbPart k r z)) := by
    refine ae_of_ae_map (p := fun ζ => Tz k r z * Tz k r z' < Complex.normSq ζ) hπm.aemeasurable ?_
    rw [hpush]
    exact Measure.ae_smul_measure (ae_weight k _ _) c
  have hcongr : ∀ᵐ u ∂σb k (Tz k r z'), ∫⁻ h, F (act h (jV k r u)) ∂μW =
      (fun ζ => ∫⁻ h, F (act h (embWb k r (μsec ζ) *ᵥ z')) ∂μW) (herm (Hb k) u (wbPart k r z)) := by
    filter_upwards [hgg, σb_conc hT'] with u hu1 hu2
    have hζ' : herm (Hpk k r) (jV k r u) z = herm (Hb k) u (wbPart k r z) := by
      rw [← herm_jV (r := r), jV_wbPart hz]
    obtain ⟨s1, s2, s3⟩ := sec_vec hz hz' hsec hu1
    have huu : herm (Hpk k r) (jV k r u) (jV k r u) = -((Tz k r z' : ℝ) : ℂ) := by
      rw [herm_jV, herm_Hb_self, hu2]
    obtain ⟨h₁, hh₁, hx⟩ := orbit hz (inWb_jV u) s1 hT.ne' (by rw [huu, s2, herm_self_eq]) (by rw [hζ', s3])
      (by
        rw [huu, hζ']
        have : (-((Tz k r z' : ℝ) : ℂ)).re = -Tz k r z' := by simp
        rw [this]
        nlinarith)
    rw [avg_orbit hW hF hh₁ (jV k r u), hx]
  rw [lintegral_congr_ae hcongr]
  have hΨm' : AEMeasurable (fun ζ => ∫⁻ h, F (act h (embWb k r (μsec ζ) *ᵥ z')) ∂μW)
      ((σb k (Tz k r z')).map fun u => herm (Hb k) u (wbPart k r z)) := by
    rw [hpush]; exact hΨm.smul_measure c
  rw [← lintegral_map' hΨm' hπm.aemeasurable, hpush, lintegral_smul_measure, smul_eq_mul]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
