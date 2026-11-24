-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.sesquilinear_polarization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:50:40.475798+00:00
-- url     : https://prove2.me/submissions/b35ce8da-0049-46f6-a825-8876bd231ef5

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable

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
    4 * β x y = β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) + Complex.I * β (x + Complex.I • y) (x + Complex.I • y)
      - β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) - Complex.I * β (x + (-Complex.I) • y) (x + (-Complex.I) • y) := by
  simp only [hl, hr, map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination (2 * β x y - 2 * β y x) * Complex.I_mul_I
end Formalism.FourierDecayAlt.P5
