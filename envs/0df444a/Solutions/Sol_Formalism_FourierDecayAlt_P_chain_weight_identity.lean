-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.chain_weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:47.987797+00:00
-- url     : https://prove2.me/submissions/ba6b6ffc-f22e-4813-8f69-217538309a17

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_chainWeight_snoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_measurable_chainWeight
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderChainWeights_ae_pi_all

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.OrderChainWeights
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.ChainIdentity := by
  intro X _ μ _ nrm Kk hn hK hae h0 hstep i
  induction i with
  | zero =>
    have hw : ∀ c : Fin 0 → X, chainWeight nrm 0 c = 1 := fun c => by simp [chainWeight]
    simp only [h0, hw, one_mul, lintegral_const, Measure.pi_univ, Finset.univ_eq_empty,
      Finset.prod_empty]
  | succ i ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (i + 1) => X) (Fin.last i) with he
    have hmp : MeasurePreserving e.symm (μ.prod (Measure.pi fun _ : Fin i => μ))
        (Measure.pi fun _ : Fin (i + 1) => μ) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (i + 1) => μ) (Fin.last i)).symm e
    rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding]
    have hFm : Measurable fun z : X × (Fin i → X) =>
        Kk (i + 1) (e.symm z) * chainWeight nrm (i + 1) (e.symm z) :=
      ((hK (i + 1)).comp e.symm.measurable).mul ((measurable_chainWeight nrm hn (i + 1)).comp e.symm.measurable)
    rw [lintegral_prod_symm _ hFm.aemeasurable]
    have hsn : ∀ (h : Fin i → X) (c : X), e.symm (c, h) = (Fin.snoc h c : Fin (i + 1) → X) := by
      intro h c
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_last' c h
    simp_rw [hsn, chainWeight_snoc]
    rw [← ih]
    apply lintegral_congr_ae
    filter_upwards [ae_pi_all μ i _ hae] with h hh
    have hmeas : Measurable fun c : X => Kk (i + 1) (Fin.snoc h c : Fin (i + 1) → X) := by
      have h1 : Measurable fun c : X => e.symm (c, h) :=
        e.symm.measurable.comp (measurable_id.prodMk measurable_const)
      simp_rw [hsn] at h1
      exact (hK (i + 1)).comp h1
    rw [lintegral_mul_const _ hmeas, hstep i h hh]
    have hP0 : (∏ l, nrm (h l)) ^ 2 ≠ 0 :=
      pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun l _ => (hh l).1)
    have hPt : (∏ l, nrm (h l)) ^ 2 ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.prod_ne_top fun l _ => (hh l).2)
    calc ((∏ l, nrm (h l)) ^ 2)⁻¹ * Kk i h * (chainWeight nrm i h * (∏ l, nrm (h l)) ^ 2)
        = Kk i h * chainWeight nrm i h * (((∏ l, nrm (h l)) ^ 2)⁻¹ * (∏ l, nrm (h l)) ^ 2) := by ring
      _ = Kk i h * chainWeight nrm i h := by rw [ENNReal.inv_mul_cancel hP0 hPt, mul_one]
end Formalism.FourierDecayAlt.P
