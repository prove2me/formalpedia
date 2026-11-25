-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_decay_of_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:07:57.976309+00:00
-- url     : https://prove2.me/submissions/8bf06f55-ff5e-41b6-855a-ae543f143dc4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_decay_of_weight
import Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_integral_iteratedFDeriv_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.FourierDecayAlt.P5.HerC.Fou
theorem _root_.solution [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (hV : finrank ℝ V ≤ 3)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ (∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  obtain ⟨hD, C, hC⟩ := decay_of_weight hE B hEb hDE
  refine ⟨hD, ⟨C, hC⟩, fun j hj1 hjm => integral_iteratedFDeriv_eq_zero hD C (fun i hi x => ?_) j hj1 hjm⟩
  refine (hC i hi x).trans ?_
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  gcongr
  · linarith [norm_nonneg x]
  · have : (finrank ℝ V : ℝ) ≤ 3 := by exact_mod_cast hV
    linarith
end Formalism.FourierDecayAlt.P5.HerC.Fou
