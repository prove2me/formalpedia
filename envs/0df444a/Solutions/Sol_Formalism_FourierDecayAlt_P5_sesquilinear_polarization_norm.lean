-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.sesquilinear_polarization_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:50.801947+00:00
-- url     : https://prove2.me/submissions/60798f4e-33e0-4a29-a248-407e117c3331

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P5_sesquilinear_polarization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    ‖β x y‖ ≤ (‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖) / 4 := by
  have h := sesquilinear_polarization β hl hr x y
  have h4 : ‖(4 : ℂ) * β x y‖ = 4 * ‖β x y‖ := by simp
  have : ‖(4 : ℂ) * β x y‖ ≤ ‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖ := by
    rw [h]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) le_rfl)) ?_
    · simp
    · simp
  linarith
end Formalism.FourierDecayAlt.P5
