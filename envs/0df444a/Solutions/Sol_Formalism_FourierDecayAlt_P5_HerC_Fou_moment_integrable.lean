-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.moment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:19.136192+00:00
-- url     : https://prove2.me/submissions/023654f4-edc9-4744-a0ce-bf1e2ab084af

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MomentIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Module
open scoped FourierTransform
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution {u : V → ℂ} (hu : Continuous u) (m : ℕ) (C : ℝ)
    (hdec : ∀ w, ‖u w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) (n : ℕ) (hn : n ≤ m) :
    Integrable (fun v => ‖v‖ ^ n * ‖u v‖) := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hdec 0)
    have hp : 0 < (1 + ‖(0 : V)‖) ^ (-((m : ℝ) + finrank ℝ V + 1)) := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hint : Integrable (fun v : V => C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1))) :=
    (integrable_one_add_norm (by linarith)).const_mul C
  refine hint.mono' ((continuous_norm.pow n).mul (continuous_norm.comp hu)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖v‖ := by linarith [norm_nonneg v]
  have h0 : (0 : ℝ) < 1 + ‖v‖ := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖v‖ ^ n * ‖u v‖ ≤ (1 + ‖v‖) ^ n * (C * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        gcongr
        · linarith [norm_nonneg v]
        · exact hdec v
    _ = C * ((1 + ‖v‖) ^ (n : ℝ) * (1 + ‖v‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) := by
        rw [Real.rpow_natCast]; ring
    _ = C * (1 + ‖v‖) ^ ((n : ℝ) + -((m : ℝ) + finrank ℝ V + 1)) := by
        rw [← Real.rpow_add h0]
    _ ≤ C * (1 + ‖v‖) ^ (-((finrank ℝ V : ℝ) + 1)) := by
        gcongr
        have : (n : ℝ) ≤ m := by exact_mod_cast hn
        linarith
end Formalism.FourierDecayAlt.P5.HerC.Fou
