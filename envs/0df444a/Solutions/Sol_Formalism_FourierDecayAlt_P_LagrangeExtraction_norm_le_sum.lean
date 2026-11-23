-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.norm_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:45.389174+00:00
-- url     : https://prove2.me/submissions/170b70f4-e8ed-4cae-8cae-34dc4ec79913

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_LagrangeExtraction_extractK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction
theorem _root_.solution {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {K d : ℕ} (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ) (hP : PolyStep K d s W)
    (hg : ∀ a, Function.Injective (grid a)) (y₀ : Fin K → ℝ) :
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      ∑ j : Fin K → Fin (d + 1), (∏ a, |lagCo (grid a) (j a)|) * ‖W K fun a => grid a (j a)‖ := by
  have h := extractK V K d s W grid hP hg y₀
  calc (∏ a, ‖s a‖) * ‖W 0 y₀‖ = ‖(∏ a, s a) • W 0 y₀‖ := by rw [norm_smul, norm_prod]
    _ = ‖∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ := by
        rw [h]
    _ ≤ ∑ j : Fin K → Fin (d + 1), ‖((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ :=
        norm_sum_le _ _
    _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
end Formalism.FourierDecayAlt.P.LagrangeExtraction
