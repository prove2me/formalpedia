-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.disc_fubini
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:36:36.842173+00:00
-- url     : https://prove2.me/submissions/f04c1f82-3832-45a5-aebf-c405f12a4b40

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_vol_sq_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {R ρ : ℝ} (hR : 0 < R) :
    ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by
  classical
  set e := Complex.measurableEquivRealProd with he
  have hpres : MeasurePreserving e.symm volume volume :=
    MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod
  set F : ℂ → ℂ := (ball (0 : ℂ) R).indicator (fun z => ee ρ z.re) with hF
  set S : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < R ^ 2} with hS
  have hmemS : ∀ p : ℝ × ℝ, e.symm p ∈ ball (0 : ℂ) R ↔ p ∈ S := by
    intro p
    rw [Complex.measurableEquivRealProd_symm_apply, mem_ball, dist_zero_right,
      Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_lt' hR]
    rfl
  have hFG : ∀ p : ℝ × ℝ, F (e.symm p) = S.indicator (fun q => ee ρ q.1) p := by
    intro p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, hF, Set.indicator_of_mem ((hmemS p).mpr hp),
        Complex.measurableEquivRealProd_symm_apply]
    · rw [Set.indicator_of_notMem hp, hF,
        Set.indicator_of_notMem (fun h => hp ((hmemS p).mp h))]
  have hcont : Continuous (fun z : ℂ => ee ρ z.re) := by
    unfold ee
    fun_prop
  have hFint : Integrable F := by
    rw [hF, integrable_indicator_iff measurableSet_ball]
    refine Measure.integrableOn_of_bounded (M := 1) measure_ball_lt_top.ne
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [ee]
    rw [Complex.norm_exp_I_mul_ofReal]
  have hGint : Integrable (S.indicator (fun q : ℝ × ℝ => ee ρ q.1)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    have h1 : (fun p => F (e.symm p)) = S.indicator (fun q : ℝ × ℝ => ee ρ q.1) := funext hFG
    rw [← h1]
    exact (hpres.integrable_comp_emb e.symm.measurableEmbedding).mpr hFint
  have hSmeas : ∀ a : ℝ, MeasurableSet {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} := fun a =>
    measurableSet_lt (by fun_prop) measurable_const
  calc ∫ z in ball (0 : ℂ) R, ee ρ z.re = ∫ z, F z := (integral_indicator measurableSet_ball).symm
    _ = ∫ p, F (e.symm p) := (hpres.integral_comp' F).symm
    _ = ∫ p, S.indicator (fun q : ℝ × ℝ => ee ρ q.1) p ∂(volume.prod volume) := by
        rw [← Measure.volume_eq_prod]
        exact integral_congr_ae (Filter.Eventually.of_forall hFG)
    _ = ∫ a, ∫ b, S.indicator (fun q : ℝ × ℝ => ee ρ q.1) (a, b) := integral_prod _ hGint
    _ = ∫ a, ((2 * Real.sqrt (R ^ 2 - a ^ 2) : ℝ) : ℂ) * ee ρ a := by
        congr 1
        funext a
        have hin : (fun b => S.indicator (fun q : ℝ × ℝ => ee ρ q.1) (a, b)) =
            {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2}.indicator (fun _ => ee ρ a) := by
          funext b
          by_cases hb : b ^ 2 < R ^ 2 - a ^ 2
          · rw [Set.indicator_of_mem (show b ∈ {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} from hb),
              Set.indicator_of_mem (show (a, b) ∈ S from show a ^ 2 + b ^ 2 < R ^ 2 by linarith)]
          · rw [Set.indicator_of_notMem (show b ∉ {b : ℝ | b ^ 2 < R ^ 2 - a ^ 2} from hb),
              Set.indicator_of_notMem (show (a, b) ∉ S from fun h => hb (by
                have h' : a ^ 2 + b ^ 2 < R ^ 2 := h
                linarith))]
        rw [hin, integral_indicator_const _ (hSmeas a), measureReal_def, vol_sq_lt,
          ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    _ = ∫ t in (-R)..R, ((2 * Real.sqrt (R ^ 2 - t ^ 2) : ℝ) : ℂ) * ee ρ t := by
        rw [intervalIntegral.integral_of_le (by linarith),
          setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro a ha
        have h2 : R ^ 2 - a ^ 2 ≤ 0 := by
          simp only [mem_Ioc, not_and_or, not_lt, not_le] at ha
          rcases ha with h | h <;> nlinarith
        rw [Real.sqrt_eq_zero'.mpr h2]
        simp
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
