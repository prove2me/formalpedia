-- Prove2me | solution 1 for Formalism.FN.GjScaling.lintegral_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:49.162822+00:00
-- url     : https://prove2.me/submissions/8014319a-1fc2-4fbc-bddc-1a272d54e00d

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
open Formalism.FN.GjScaling
variable {ι : Type*} [Fintype ι]
namespace Formalism.FN.GjScaling
theorem _root_.solution {κ : Type*} [Fintype κ] (h : (κ → ℝ) → ℝ≥0∞) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, h y = ENNReal.ofReal (s ^ Fintype.card κ) * ∫⁻ y, h (s • y) := by
  have hs0 : s ≠ 0 := hs.ne'
  have e1 : ∫⁻ y, h (s • y) = ∫⁻ y, h y ∂(Measure.map (fun x : κ → ℝ => s • x) volume) :=
    (lintegral_map_equiv h (Homeomorph.smulOfNeZero s hs0).toMeasurableEquiv).symm
  rw [Measure.map_addHaar_smul (μ := volume) hs0, lintegral_smul_measure, smul_eq_mul,
    Module.finrank_fintype_fun_eq_card] at e1
  rw [e1, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos hs _).le, abs_of_pos (inv_pos.2 (pow_pos hs _)),
    mul_inv_cancel₀ (pow_ne_zero _ hs0), ENNReal.ofReal_one, one_mul]
end Formalism.FN.GjScaling
