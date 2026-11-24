-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.engine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:46:36.868872+00:00
-- url     : https://prove2.me/submissions/582d0cf2-ef30-4e53-98f1-f7b96e62a6f8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_zW_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_cW_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_cW_nonneg

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas sgF_meas
set_option maxHeartbeats 800000
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution {μG μN μb μW μW' : Measure (Mt k r)} [SFinite μN] [SFinite μb] [SFinite μW] [SFinite μW'] (T T' : ℝ)
    (G0 : (Fin r → ℂ) → Mt k r) (hG0 : Measurable G0) (ES : ℂ → Mt k r) (hES : Measurable ES) (C1 C2 : ℝ≥0)
    (hIt : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = (C1 : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ,
      ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb))
    (hR : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ m, f m ∂μb = (C2 : ℝ≥0∞) * ∫⁻ ζ : ℂ,
      ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ p : Mt k r × Mt k r, f (mulM (mulM (invM p.1, ES ζ), p.2)) ∂(μW.prod μW'))
    (hkey : ∀ (c : Fin r → ℂ) (ζ : ℂ) (f : Mt k r → ℝ≥0∞), Measurable f →
      ∫⁻ nn : Mt k r × Mt k r, ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2))
          ∂(μW.prod μW') ∂(μN.prod μN) =
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)))
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μG = ((C1 * C2 : ℝ≥0) : ℝ≥0∞) * ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (cWeight k r q.1 * zWeight k T T' q.2) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) := by
  have hcw : Measurable (cWeight k r) := cW_cont.measurable
  have hzw : Measurable (zWeight k T T') := zW_meas k T T'
  have hKm : Measurable fun q : (Fin r → ℂ) × ℂ =>
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    (by fun_prop : Measurable fun x : ((Fin r → ℂ) × ℂ) × SS k r =>
      f (sgF (x.2, mulM (G0 x.1.1, ES x.1.2)))).lintegral_prod_right'
  have hA : ∀ c : Fin r → ℂ, ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
      f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) =
      (C2 : ℝ≥0∞) * ∫⁻ ζ, ENNReal.ofReal (zWeight k T T' ζ) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    intro c
    have hIm : Measurable fun y : (Mt k r × Mt k r) × ℂ => ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM y.1.1, G0 c), mulM (mulM (invM hh.1, ES y.2), hh.2)), y.1.2)) ∂(μW.prod μW') :=
      (by fun_prop : Measurable fun x : ((Mt k r × Mt k r) × ℂ) × (Mt k r × Mt k r) =>
        f (mulM (mulM (mulM (invM x.1.1.1, G0 c), mulM (mulM (invM x.2.1, ES x.1.2), x.2.2)), x.1.1.2))).lintegral_prod_right'
    have hJ : Measurable fun y : (Mt k r × Mt k r) × ℂ => ENNReal.ofReal (zWeight k T T' y.2) *
        ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM y.1.1, G0 c), mulM (mulM (invM hh.1, ES y.2), hh.2)), y.1.2)) ∂(μW.prod μW') :=
      (hzw.comp measurable_snd).ennreal_ofReal.mul hIm
    have hJx : Measurable fun nn : Mt k r × Mt k r => ∫⁻ ζ, ENNReal.ofReal (zWeight k T T' ζ) *
        ∫⁻ hh : Mt k r × Mt k r, f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW') :=
      hJ.lintegral_prod_right'
    rw [lintegral_prod _ (by fun_prop : Measurable fun x : (Mt k r × Mt k r) × Mt k r =>
      f (mulM (mulM (mulM (invM x.1.1, G0 c), x.2), x.1.2))).aemeasurable]
    refine Eq.trans (lintegral_congr fun nn =>
      hR (fun m => f (mulM (mulM (mulM (invM nn.1, G0 c), m), nn.2))) (by fun_prop)) ?_
    rw [lintegral_const_mul _ hJx, lintegral_lintegral_swap (f := fun (nn : Mt k r × Mt k r) (ζ : ℂ) =>
      ENNReal.ofReal (zWeight k T T' ζ) * ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW'))
      hJ.aemeasurable]
    refine congrArg (fun t => (C2 : ℝ≥0∞) * t) ?_
    refine lintegral_congr fun ζ => ?_
    have hC : Measurable fun nn : Mt k r × Mt k r => ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, G0 c), mulM (mulM (invM hh.1, ES ζ), hh.2)), nn.2)) ∂(μW.prod μW') :=
      (by fun_prop : Measurable fun x : (Mt k r × Mt k r) × (Mt k r × Mt k r) =>
        f (mulM (mulM (mulM (invM x.1.1, G0 c), mulM (mulM (invM x.2.1, ES ζ), x.2.2)), x.1.2))).lintegral_prod_right'
    rw [lintegral_const_mul _ hC, hkey c ζ f hf]
  have hD : ∀ c : Fin r → ℂ, Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ) *
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) := fun c => by
    have hK' : Measurable fun ζ : ℂ => ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
      (by fun_prop : Measurable fun x : ℂ × SS k r => f (sgF (x.2, mulM (G0 c, ES x.1)))).lintegral_prod_right'
    exact hzw.ennreal_ofReal.mul hK'
  have hB : ∀ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f (mulM (mulM (mulM (invM p.1.1, G0 c), p.2), p.1.2)) ∂((μN.prod μN).prod μb) =
      (C2 : ℝ≥0∞) * ∫⁻ ζ, ENNReal.ofReal (cWeight k r c * zWeight k T T' ζ) *
        ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) := fun c => by
    rw [hA c, ← mul_assoc, mul_comm (ENNReal.ofReal (cWeight k r c)) (C2 : ℝ≥0∞), mul_assoc,
      ← lintegral_const_mul _ (hD c)]
    refine congrArg (fun t => (C2 : ℝ≥0∞) * t) ?_
    refine lintegral_congr fun ζ => ?_
    rw [ENNReal.ofReal_mul (cW_nonneg c), mul_assoc]
  have hQ : Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (cWeight k r q.1 * zWeight k T T' q.2) *
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 q.1, ES q.2))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    ((hcw.comp measurable_fst).mul (hzw.comp measurable_snd)).ennreal_ofReal.mul hKm
  have hE : Measurable fun c : Fin r → ℂ => ∫⁻ ζ, ENNReal.ofReal (cWeight k r c * zWeight k T T' ζ) *
      ∫⁻ p : SS k r, f (sgF (p, mulM (G0 c, ES ζ))) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    hQ.lintegral_prod_right'
  rw [hIt f hf, lintegral_congr hB, lintegral_const_mul _ hE, Measure.volume_eq_prod,
    lintegral_prod _ hQ.aemeasurable, ENNReal.coe_mul, mul_assoc]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
