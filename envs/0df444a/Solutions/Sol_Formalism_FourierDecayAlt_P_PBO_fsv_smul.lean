-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBO.fsv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:29.820914+00:00
-- url     : https://prove2.me/submissions/b904a260-5867-4515-8d35-7514d36510ee

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormLeIntegralFsv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBO_isoQ_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBO
namespace Formalism.FourierDecayAlt.P.PBO
theorem _root_.solution (s u z : ℂ) : P5.fsv s u * z = 𝐞 (-⟪u, (π⁻¹ : ℝ) • isoQ s⟫) • z := by
  unfold P5.fsv
  simp [Circle.smul_def, isoQ_apply]
  left
  rw [Real.fourierChar_apply]
  congr 1
  have hπ : π ≠ 0 := Real.pi_ne_zero
  apply Complex.ext <;> simp <;> field_simp <;> ring
end Formalism.FourierDecayAlt.P.PBO
